#!/usr/bin/env bash
# Engineering local-node gate for XrplCtx environment leaves.
# Missing docker/bedrock → skip (exit 0). Deploys ProofForge XrplCtx.wasm only.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

xrpl_init xrpl-local-ctx

wasm="$root/build/xrpl/XrplCtx.wasm"
fixture="$here/fixture"
staged="$fixture/contract/target/wasm32-unknown-unknown/release/Counter.wasm"

if [[ ! -f "$wasm" ]]; then
  echo "xrpl-local-ctx: building XrplCtx.wasm" >&2
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

echo "xrpl-local-ctx: starting local node" >&2
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

stamp_out="$(xrpl_call stamp '{}')"
xrpl_require_equal "$(xrpl_call_code "$stamp_out")" "0" "stamp status"

sqn="$(xrpl_slot_u64 "$owner" "$contract" "stamped")"
[[ "$sqn" =~ ^[0-9]+$ ]] || { echo "FAIL: stamped is not a number: $sqn" >&2; exit 1; }
[[ "$sqn" -gt 0 ]] || { echo "FAIL: stamped ledger sqn was $sqn" >&2; exit 1; }

echo "xrpl-local-ctx: ok (stamp wrote ledger sqn=$sqn; engineering only)"
