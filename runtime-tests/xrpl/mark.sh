#!/usr/bin/env bash
# Live AlphaNet engineering gate for zero-parameter XrplMark (owner-gated hash).
# Public RPC 502s ContractCall with Parameters; this program has none.
# Sequence: initialize → stamp (hashed=SHA-512Half("vault") lo64)
#           → renounce → stamp (vmReturnCode=3, hashed unchanged).
# Missing node / unfunded wallet / RPC down → skip (exit 0), not pass.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-mark: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-mark: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
# SHA-512("vault")[:32] first 8 bytes little-endian. Same pin as hash.sh.
want="4898221643817197762"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-mark: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-mark: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-mark: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplMark.wasm"
if [[ ! -f "$wasm" ]]; then
  echo "xrpl-alphanet-mark: building XrplMark.wasm" >&2
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplMark
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

slot_hashed() {
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"hashed"}\n' \
    "$RPC" "$OWNER" "$contract" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

stamp_out="$(call_fn stamp)"
echo "$stamp_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$stamp_out"
hashed="$(slot_hashed)"
[[ "$hashed" == "$want" ]] || { echo "FAIL: expected hashed=$want after stamp, got $hashed" >&2; exit 1; }

renounce_out="$(call_fn renounce)"
echo "$renounce_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$renounce_out"

denied_out="$(call_fn stamp)"
echo "$denied_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$denied_out"
hashed="$(slot_hashed)"
rm -f "$cfg"
[[ "$hashed" == "$want" ]] || { echo "FAIL: expected hashed=$want after denied stamp, got $hashed" >&2; exit 1; }

echo "xrpl-alphanet-mark: ok contract=$contract hashed=$want unauthorized=3"
