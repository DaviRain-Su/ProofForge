#!/usr/bin/env bash
# Probe set_data_object_field targeting another AccountID (hardcoded).
# Not setUserData. Not Sdk.Map. RPC down → skip. Missing import → fail closed.
# Host reject is a recorded outcome (probe, not a digest gate).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-probe-other: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-probe-other: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-other: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OTHER="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"
OTHER_SEED="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-probe-other: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-probe-other: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-probe-other: $RPC $info" >&2

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-other.wasm"
"$wat2wasm" "$here/fixture/probe-other.wat" -o "$wasm"

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: ContractCreate rejected set_data_object_field" >&2
  echo "$deploy_out" >&2
  rm -f "$cfg"
  exit 1
fi
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"

call_fn() {
  local fn="$1"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg" || true
}

init_out="$(call_fn initialize)"
echo "initialize $init_out" >&2

poke_out="$(call_fn poke)"
echo "poke $poke_out" >&2
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$poke_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$poke_out")"

# Other account may not exist yet; fund so account_objects can be queried.
printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","destination":"%s","drops":"20000000"}\n' \
  "$RPC" "$WALLET" "$OTHER" >"$cfg"
node "$here/alphanet-rpc.js" pay "$cfg" >/dev/null 2>&1 || true

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OTHER" "$contract" >"$cfg"
slot="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo "missing")"
rm -f "$cfg"

echo "xrpl-probe-other: poke result=$result vmReturnCode=$code slot_on_other=$slot" >&2
if [[ "$result" == "tesSUCCESS" && "$code" == "0" && "$slot" != "0" && "$slot" != "missing" ]]; then
  echo "xrpl-probe-other: ok contract=$contract WRITE_OTHER=green slot=$slot. Still not Sdk.Map."
  exit 0
fi
# Host ran. Negative code / empty slot = cannot write another user's card.
echo "xrpl-probe-other: ok contract=$contract WRITE_OTHER=$result/$code slot=$slot (not green; no Sdk.Map)"
