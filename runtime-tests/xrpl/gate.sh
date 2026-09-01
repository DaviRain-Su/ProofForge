#!/usr/bin/env bash
# Live AlphaNet engineering gate for zero-parameter XrplGate (Ownable + renounce).
# Public RPC 502s ContractCall with Parameters; this program has none.
# Sequence: initialize → bump (value=1) → renounce → bump (vmReturnCode=3, value stays 1).
# Missing node / unfunded wallet / RPC down → skip (exit 0), not pass.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-gate: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-gate: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-gate: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-gate: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-gate: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplGate.wasm"
if [[ ! -f "$wasm" ]]; then
  echo "xrpl-alphanet-gate: building XrplGate.wasm" >&2
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplGate
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount: $deploy_out" >&2
  exit 1
}

call_fn() {
  local fn="$1"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

bump_out="$(call_fn bump)"
echo "$bump_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$bump_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"value"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
value="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1 after bump, got $value" >&2; exit 1; }

renounce_out="$(call_fn renounce)"
echo "$renounce_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$renounce_out"

denied_out="$(call_fn bump)"
echo "$denied_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$denied_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"value"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
value="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1 after denied bump, got $value" >&2; exit 1; }

echo "xrpl-alphanet-gate: ok contract=$contract value=1 unauthorized=3"
