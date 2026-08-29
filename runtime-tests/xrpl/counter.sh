#!/usr/bin/env bash
# Engineering local-node gate for Counter. Darwin + Linux.
# Missing docker/bedrock → skip (exit 0), not pass.
# Deploys ProofForge Counter.wasm only (--skip-build); never runs bedrock build.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

xrpl_init xrpl-local-counter

UINT64_MAX="18446744073709551615"
wasm="$root/build/xrpl/Counter.wasm"
fixture="$here/fixture"
staged="$fixture/contract/target/wasm32-unknown-unknown/release/Counter.wasm"

if [[ ! -f "$wasm" ]]; then
  echo "xrpl-local-counter: building Counter.wasm" >&2
  lake exe pf -- build --target xrpl --out "$root/build/xrpl"
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }
"$python" -I -S -c '
import sys
raise SystemExit(0 if open(sys.argv[1], "rb").read(4) == b"\x00asm" else 1)
' "$wasm" || { echo "FAIL: $wasm is not wasm" >&2; exit 1; }

mkdir -p "$(dirname "$staged")"
cp -f "$wasm" "$staged"
# bedrock node start bind-mounts config_dir/xrpld.cfg; if the host path is
# missing Docker creates a directory and rippled SIGSEGVs. Seed the files.
mkdir -p "$fixture/.bedrock/node-config"
rm -rf "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/xrpld.cfg" "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/genesis.json" "$fixture/.bedrock/node-config/genesis.json"

cleanup() {
  if [[ -n "${bedrock:-}" ]]; then
    (cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
  fi
}
trap cleanup EXIT

echo "xrpl-local-counter: starting local node" >&2
(cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
(cd "$fixture" && "$bedrock" node start)

wallet="$(xrpl_genesis_seed)"
owner="$(xrpl_genesis_address)"

deploy_out="$(cd "$fixture" && "$bedrock" deploy \
  --network local \
  --skip-build \
  --skip-abi \
  --abi abi.json \
  --wallet "$wallet")"
echo "$deploy_out" >&2

contract="$(xrpl_field "$deploy_out" "Contract Account")"
[[ -n "$contract" ]] || {
  echo "FAIL: deploy did not return Contract Account: $deploy_out" >&2
  exit 1
}

xrpl_call() {
  local fn="$1"
  local params="{}"
  if [[ -n "${2:-}" ]]; then
    params="$2"
  fi
  local cfg
  cfg="$(mktemp)"
  XRPL_CFG="$cfg" \
  XRPL_CONTRACT="$contract" XRPL_FN="$fn" XRPL_WALLET="$wallet" \
    XRPL_ABI="$fixture/abi.json" XRPL_PARAMS="$params" \
    "$python" -I -S -c '
import json, os
json.dump({
    "contract_account": os.environ["XRPL_CONTRACT"],
    "function_name": os.environ["XRPL_FN"],
    "network_url": "ws://localhost:6006",
    "wallet_seed": os.environ["XRPL_WALLET"],
    "abi_path": os.environ["XRPL_ABI"],
    "parameters": json.loads(os.environ.get("XRPL_PARAMS") or "{}"),
}, open(os.environ["XRPL_CFG"], "w", encoding="utf-8"))
'
  local out
  out="$(node "$here/call.js" "$cfg")"
  rm -f "$cfg"
  printf '%s\n' "$out"
}

xrpl_call_code() {
  "$python" -I -S -c 'import json,sys; print(json.load(sys.stdin).get("returnCode"))' <<<"$1"
}

xrpl_call_value() {
  "$python" -I -S -c '
import json, sys
obj = json.load(sys.stdin)
v = obj.get("returnValue")
if v is None or v == "":
    print(0)
    raise SystemExit
if isinstance(v, int):
    print(v)
    raise SystemExit
s = str(v)
if s.startswith("0x") or s.startswith("0X"):
    s = s[2:]
try:
    print(int(s, 16) if s else 0)
except ValueError:
    print(s)
' <<<"$1"
}

init_out="$(xrpl_call initialize '{"initial_value":"0"}')"
xrpl_require_equal "$(xrpl_call_code "$init_out")" "0" "initialize status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract")" "0" "initialize state"

get0="$(xrpl_call get '{}')"
xrpl_require_equal "$(xrpl_call_code "$get0")" "0" "get after init status"

inc_out="$(xrpl_call increment '{"amount":"1"}')"
xrpl_require_equal "$(xrpl_call_code "$inc_out")" "0" "increment status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract")" "1" "increment state"

max_init="$(xrpl_call initialize "{\"initial_value\":\"$UINT64_MAX\"}")"
xrpl_require_equal "$(xrpl_call_code "$max_init")" "0" "max initialize status"
set +e
ovf="$(xrpl_call increment '{"amount":"1"}')"
ovf_status=$?
set -e
if [[ "$ovf_status" -eq 0 ]]; then
  xrpl_require_equal "$(xrpl_call_code "$ovf")" "1" "overflow increment status"
fi
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract")" "$UINT64_MAX" \
  "overflow must leave counter"

echo "xrpl-local-counter: ok (initialize/get/increment/overflow; engineering only)"
