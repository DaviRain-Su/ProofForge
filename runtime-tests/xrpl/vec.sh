#!/usr/bin/env bash
# Engineering local-node gate for XrplVec compile-time named JSON slots.
# Missing docker/bedrock → skip (exit 0). Deploys ProofForge XrplVec.wasm only.
# setAt writes xs_0 / xs_1 / xs_2; index 3 returns overflow status 1.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

xrpl_init xrpl-local-vec

wasm="$root/build/xrpl/XrplVec.wasm"
fixture="$here/fixture"
staged="$fixture/contract/target/wasm32-unknown-unknown/release/Counter.wasm"

if [[ ! -f "$wasm" ]]; then
  echo "xrpl-local-vec: building XrplVec.wasm" >&2
  lake exe pf -- build --target xrpl --out "$root/build/xrpl"
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

mkdir -p "$(dirname "$staged")"
cp -f "$wasm" "$staged"
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

echo "xrpl-local-vec: starting local node" >&2
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

init_out="$(xrpl_call initialize '{"initial_value":"0"}')"
xrpl_require_equal "$(xrpl_call_code "$init_out")" "0" "initialize status"

set0="$(xrpl_call setAt '{"index":"0","value":"11"}')"
xrpl_require_equal "$(xrpl_call_code "$set0")" "0" "setAt 0 status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_0")" "11" "xs_0 after setAt 0"

set1="$(xrpl_call setAt '{"index":"1","value":"22"}')"
xrpl_require_equal "$(xrpl_call_code "$set1")" "0" "setAt 1 status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_1")" "22" "xs_1 after setAt 1"

set2="$(xrpl_call setAt '{"index":"2","value":"33"}')"
xrpl_require_equal "$(xrpl_call_code "$set2")" "0" "setAt 2 status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_2")" "33" "xs_2 after setAt 2"

# Neighbours must stay put.
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_0")" "11" "xs_0 unchanged by later writes"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_1")" "22" "xs_1 unchanged by later writes"

bad="$(xrpl_call setAt '{"index":"3","value":"99"}')"
xrpl_require_equal "$(xrpl_call_code "$bad")" "1" "setAt 3 overflow status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_0")" "11" "xs_0 after overflow"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_1")" "22" "xs_1 after overflow"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "xs_2")" "33" "xs_2 after overflow"

echo "xrpl-local-vec: ok (xs_0=11 xs_1=22 xs_2=33; engineering only)"
