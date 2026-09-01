#!/usr/bin/env bash
set -euo pipefail
umask 077

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

surfpool_version="1.5.0"
rpc_url="http://127.0.0.1:8899"
out_dir="build/surfpool"
manifest="runtime-tests/surfpool/txtx.yml"
program_name="${1:-Phoenix}"

case "$program_name" in
  Phoenix|PhoenixV1Profile|RawEntry|Info|LamportTransfer|FeatureBits|MemberDirectory|VersionedLedger|BatchSizer) ;;
  *)
    echo "surfpool-smoke: supported programs: Phoenix, PhoenixV1Profile, RawEntry, Info, LamportTransfer, FeatureBits, MemberDirectory, VersionedLedger, BatchSizer" >&2
    exit 1
    ;;
esac

for tool in curl jq lake openssl python3 surfpool; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "surfpool-smoke: missing required tool: $tool" >&2
    exit 1
  fi
done
if [[ "$(surfpool --version)" != "surfpool ${surfpool_version}" ]]; then
  echo "surfpool-smoke: expected Surfpool ${surfpool_version}, got $(surfpool --version)" >&2
  exit 1
fi

generate_keypair() {
  local destination="$1"
  local private_der public_der
  private_der="$(mktemp)"
  public_der="$(mktemp)"
  openssl genpkey -algorithm ED25519 -outform DER -out "$private_der" 2>/dev/null
  openssl pkey -inform DER -in "$private_der" -pubout -outform DER -out "$public_der" 2>/dev/null
  python3 - "$private_der" "$public_der" "$destination" <<'PY'
import json
import pathlib
import sys

private_der = pathlib.Path(sys.argv[1]).read_bytes()
public_der = pathlib.Path(sys.argv[2]).read_bytes()
secret = private_der[-32:] + public_der[-32:]
if len(secret) != 64:
    raise SystemExit("invalid Ed25519 keypair length")
pathlib.Path(sys.argv[3]).write_text(json.dumps(list(secret)) + "\n")
PY
  rm -f "$private_der" "$public_der"
}

keypair_pubkey() {
  python3 - "$1" <<'PY'
import json
import pathlib
import sys

alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
keypair = bytes(json.loads(pathlib.Path(sys.argv[1]).read_text()))
public_key = keypair[32:]
number = int.from_bytes(public_key, "big")
encoded = ""
while number:
    number, digit = divmod(number, 58)
    encoded = alphabet[digit] + encoded
leading_zeroes = len(public_key) - len(public_key.lstrip(b"\0"))
print("1" * leading_zeroes + (encoded or "1"))
PY
}

rpc() {
  curl --fail-with-body --silent --show-error \
    -H 'content-type: application/json' \
    --data-binary "$1" \
    "$rpc_url"
}

rm -rf "$out_dir"
mkdir -p "$out_dir"
generate_keypair "$out_dir/payer.json"
generate_keypair "$out_dir/Program-keypair.json"
program_id="$(keypair_pubkey "$out_dir/Program-keypair.json")"

lake exe pf -- build --target svm --out "$out_dir" "$program_name"
cp "$out_dir/${program_name}.so" "$out_dir/Program.so"

surfpool start \
  --offline \
  --no-deploy \
  --no-tui \
  --no-studio \
  --disable-instruction-profiling \
  --host 127.0.0.1 \
  --port 8899 \
  --ws-port 8900 \
  --airdrop-keypair-path "$out_dir/payer.json" \
  --airdrop-amount 10000000000000 \
  --log-path "$out_dir/logs" \
  >"$out_dir/surfpool.log" 2>&1 &
surfpool_pid=$!
cleanup() {
  local status=$?
  kill "$surfpool_pid" 2>/dev/null || true
  for _ in {1..50}; do
    if ! kill -0 "$surfpool_pid" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done
  if kill -0 "$surfpool_pid" 2>/dev/null; then
    kill -KILL "$surfpool_pid" 2>/dev/null || true
  fi
  wait "$surfpool_pid" 2>/dev/null || true
  rm -f "$out_dir/payer.json" "$out_dir/Program-keypair.json" "$out_dir/deployment.log"
  return "$status"
}
trap cleanup EXIT

ready=false
for _ in $(seq 1 150); do
  if ! kill -0 "$surfpool_pid" 2>/dev/null; then
    echo "surfpool-smoke: Surfpool exited during startup" >&2
    tail -100 "$out_dir/surfpool.log" >&2
    exit 1
  fi
  health="$(rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' 2>/dev/null || true)"
  version="$(rpc '{"jsonrpc":"2.0","id":2,"method":"getVersion"}' 2>/dev/null || true)"
  if jq -e '.result == "ok"' >/dev/null 2>&1 <<<"$health" &&
      jq -e '.result."solana-core" | type == "string"' >/dev/null 2>&1 <<<"$version"; then
    ready=true
    break
  fi
  sleep 0.2
done
if [[ "$ready" != true ]]; then
  echo "surfpool-smoke: Surfpool RPC did not become ready" >&2
  tail -100 "$out_dir/surfpool.log" >&2
  exit 1
fi

echo "surfpool-smoke: submitting Loader-v3 deployment transactions"
if ! surfpool run deployment \
    --manifest-file-path "$manifest" \
    --env localnet \
    --unsupervised \
    --force \
    --output-json \
    >"$out_dir/deployment.log" 2>&1; then
  tail -100 "$out_dir/deployment.log" >&2
  exit 1
fi
sed -n '/^→ {$/,$p' "$out_dir/deployment.log" | sed '1s/^→ //' \
  >"$out_dir/deployment-output.json"
jq -e --arg program "$program_id" '
  .program_id.value == $program and
  (.signatures.value.create_buffer | length) == 1 and
  (.signatures.value.write_to_buffer | length) > 0 and
  (.signatures.value.deploy_program | length) == 1 and
  (.signatures.value.transfer_program_authority | length) == 1
' >/dev/null "$out_dir/deployment-output.json"
deploy_signature="$(jq -r '.signatures.value.deploy_program[0]' \
  "$out_dir/deployment-output.json")"

account_request="$(jq -nc --arg program "$program_id" '{
  jsonrpc: "2.0",
  id: 2,
  method: "getAccountInfo",
  params: [$program, {encoding: "base64", commitment: "confirmed"}]
}')"
account=""
for _ in $(seq 1 100); do
  account="$(rpc "$account_request")"
  if jq -e '
      .error == null and
      .result.value != null and
      .result.value.executable == true and
      .result.value.owner == "BPFLoaderUpgradeab1e11111111111111111111111" and
      .result.value.space == 36
    ' >/dev/null 2>&1 <<<"$account"; then
    break
  fi
  sleep 0.2
done
jq -e '
  .error == null and
  .result.value != null and
  .result.value.executable == true and
  .result.value.owner == "BPFLoaderUpgradeab1e11111111111111111111111" and
  .result.value.space == 36
' >/dev/null <<<"$account"
jq '.' <<<"$account" >"$out_dir/program-account.json"

programdata_id="$(python3 - "$out_dir/program-account.json" <<'PY'
import base64
import json
import pathlib
import sys

alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
account = json.loads(pathlib.Path(sys.argv[1]).read_text())
data = base64.b64decode(account["result"]["value"]["data"][0])
if len(data) != 36 or int.from_bytes(data[:4], "little") != 2:
    raise SystemExit("program account is not Loader-v3 Program state")
public_key = data[4:]
number = int.from_bytes(public_key, "big")
encoded = ""
while number:
    number, digit = divmod(number, 58)
    encoded = alphabet[digit] + encoded
leading_zeroes = len(public_key) - len(public_key.lstrip(b"\0"))
print("1" * leading_zeroes + (encoded or "1"))
PY
)"
programdata_request="$(jq -nc --arg programdata "$programdata_id" '{
  jsonrpc: "2.0",
  id: 3,
  method: "getAccountInfo",
  params: [$programdata, {encoding: "base64", commitment: "confirmed"}]
}')"
rpc "$programdata_request" >"$out_dir/programdata-account.json"
python3 - "$out_dir/programdata-account.json" "$out_dir/Program.so" <<'PY'
import base64
import json
import pathlib
import sys

account = json.loads(pathlib.Path(sys.argv[1]).read_text())
value = account.get("result", {}).get("value")
if value is None:
    raise SystemExit("missing Loader-v3 ProgramData account")
if value["owner"] != "BPFLoaderUpgradeab1e11111111111111111111111":
    raise SystemExit("ProgramData account has the wrong owner")
if value["executable"]:
    raise SystemExit("ProgramData account must not be executable")
data = base64.b64decode(value["data"][0])
elf = pathlib.Path(sys.argv[2]).read_bytes()
if value["space"] != len(elf) + 45 or data[:4] != (3).to_bytes(4, "little"):
    raise SystemExit("ProgramData account has the wrong Loader-v3 layout")
if data[45:] != elf:
    raise SystemExit("deployed ProgramData bytes differ from Program.so")
PY

signature_request="$(jq -nc --arg signature "$deploy_signature" '{
  jsonrpc: "2.0",
  id: 4,
  method: "getSignatureStatuses",
  params: [[$signature], {searchTransactionHistory: true}]
}')"
signature_status="$(rpc "$signature_request")"
jq -e '
  .error == null and
  .result.value[0] != null and
  .result.value[0].err == null and
  (.result.value[0].confirmationStatus == "confirmed" or
    .result.value[0].confirmationStatus == "finalized")
' >/dev/null <<<"$signature_status"
jq '.' <<<"$signature_status" >"$out_dir/deploy-signature-status.json"

echo "surfpool-smoke: ok"
echo "surfpool-smoke: version=$(surfpool --version)"
echo "surfpool-smoke: program=$program_name"
echo "surfpool-smoke: program_id=$program_id"
echo "surfpool-smoke: programdata_id=$programdata_id"
echo "surfpool-smoke: elf_bytes=$(wc -c <"$out_dir/Program.so")"
echo "surfpool-smoke: loader_writes=$(jq '.signatures.value.write_to_buffer | length' \
  "$out_dir/deployment-output.json")"
echo "surfpool-smoke: deploy_signature=$deploy_signature"
