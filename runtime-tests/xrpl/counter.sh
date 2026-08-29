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

cleanup() {
  if [[ -n "${bedrock:-}" ]]; then
    (cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
  fi
}
trap cleanup EXIT

echo "xrpl-local-counter: starting local node" >&2
(cd "$fixture" && "$bedrock" node start)

deploy_out="$(cd "$fixture" && "$bedrock" deploy \
  --network local \
  --skip-build \
  --skip-abi \
  --abi abi.json)"
echo "$deploy_out" >&2

contract="$(xrpl_json_field "$deploy_out" ".data.contractAccount")"
wallet="$(xrpl_json_field "$deploy_out" ".data.walletSeed")"
[[ -n "$contract" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount: $deploy_out" >&2
  exit 1
}

xrpl_call() {
  local fn="$1" params="${2:-}"
  if [[ -n "$params" ]]; then
    (cd "$fixture" && "$bedrock" call "$contract" "$fn" \
      --network local --wallet "$wallet" --abi abi.json --params "$params")
  else
    (cd "$fixture" && "$bedrock" call "$contract" "$fn" \
      --network local --wallet "$wallet" --abi abi.json)
  fi
}

init_out="$(xrpl_call initialize '{"initial_value":"0"}')"
xrpl_require_equal "$(xrpl_json_field "$init_out" ".data.returnCode")" "0" \
  "initialize status"

get0="$(xrpl_call get)"
xrpl_require_equal "$(xrpl_json_field "$get0" ".data.returnCode")" "0" "get after init status"
xrpl_require_equal "$(xrpl_hex_u64 "$(xrpl_json_field "$get0" ".data.returnValue")")" "0" \
  "initialize state"

inc_out="$(xrpl_call increment '{"amount":"1"}')"
xrpl_require_equal "$(xrpl_json_field "$inc_out" ".data.returnCode")" "0" \
  "increment status"

get1="$(xrpl_call get)"
xrpl_require_equal "$(xrpl_hex_u64 "$(xrpl_json_field "$get1" ".data.returnValue")")" "1" \
  "increment state"

max_init="$(xrpl_call initialize "{\"initial_value\":\"$UINT64_MAX\"}")"
xrpl_require_equal "$(xrpl_json_field "$max_init" ".data.returnCode")" "0" \
  "max initialize status"
set +e
ovf="$(xrpl_call increment '{"amount":"1"}')"
ovf_status=$?
set -e
if [[ "$ovf_status" -eq 0 ]]; then
  ovf_code="$(xrpl_json_field "$ovf" ".data.returnCode")"
  xrpl_require_equal "$ovf_code" "1" "overflow increment status"
fi
get_max="$(xrpl_call get)"
xrpl_require_equal "$(xrpl_hex_u64 "$(xrpl_json_field "$get_max" ".data.returnValue")")" "$UINT64_MAX" \
  "overflow must leave counter"

echo "xrpl-local-counter: ok (initialize/get/increment/overflow; engineering only)"
