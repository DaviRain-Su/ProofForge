#!/usr/bin/env bash
# Live AlphaNet: owner + operator, same-wallet self-op.
# initialize → bump (value=1) → setOp → bump (value=2).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-role: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-role: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-role: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-role: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-role: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplRole.wasm"
if [[ ! -f "$wasm" ]]; then
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplRole
fi

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"

call_fn() {
  local fn="$1"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg"
}

slot_of() {
  local key="$1"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"%s"}\n' \
    "$RPC" "$OWNER" "$contract" "$key" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

bump_out="$(call_fn bump)"
echo "$bump_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$bump_out"
value="$(slot_of value)"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1 after owner bump, got $value" >&2; exit 1; }

setop_out="$(call_fn setOp)"
echo "$setop_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$setop_out"

bump2="$(call_fn bump)"
echo "$bump2" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$bump2"
value="$(slot_of value)"
rm -f "$cfg"
[[ "$value" == "2" ]] || { echo "FAIL: expected value=2 after setOp bump, got $value" >&2; exit 1; }

echo "xrpl-alphanet-role: ok contract=$contract value=$value (self-op)"
