#!/usr/bin/env bash
# Probe whether AlphaNet set_data_object_field can target contract account
# vs caller. Not Sdk.Map. RPC down → skip. Host reject → print code, exit 0
# with a recorded outcome (this is a probe, not a digest gate).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-probe-owner: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-probe-owner: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-owner: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
CALLER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-probe-owner: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-probe-owner: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-probe-owner: $RPC $info" >&2

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-owner.wasm"
"$wat2wasm" "$here/fixture/probe-owner.wat" -o "$wasm"

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount" >&2
  exit 1
}

call_fn() {
  local fn="$1"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg" || true
}

slot_on() {
  local owner="$1"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
    "$RPC" "$owner" "$contract" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg" || echo "missing"
}

init_out="$(call_fn initialize)"
echo "initialize $init_out" >&2

caller_out="$(call_fn pokeCaller)"
echo "pokeCaller $caller_out" >&2
caller_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$caller_out")"
caller_slot="$(slot_on "$CALLER")"
echo "xrpl-probe-owner: pokeCaller code=$caller_code slot_on_caller=$caller_slot" >&2

self_out="$(call_fn pokeSelf)"
echo "pokeSelf $self_out" >&2
self_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$self_out")"
self_slot="$(slot_on "$contract")"
echo "xrpl-probe-owner: pokeSelf code=$self_code slot_on_contract=$self_slot" >&2

rm -f "$cfg"
echo "xrpl-probe-owner: ok contract=$contract caller_write=$caller_code/$caller_slot self_write=$self_code/$self_slot"
