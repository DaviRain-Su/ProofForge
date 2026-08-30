#!/usr/bin/env bash
# Live AlphaNet: compile-time slots xs_0..xs_3 via parameterized setAt.
# setAt(index, value) needs Function ABI with two UINT64s. Missing RPC → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-tab: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-tab: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-tab: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-tab: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-tab: $RPC $info" >&2

echo "xrpl-alphanet-tab: building XrplTab.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplTab
wasm="$root/build/xrpl-alphanet/XrplTab.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"setAt":2}}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount" >&2
  exit 1
}

# setAt(3, 7) → xs_3 = 7. Do not call initialize (zero slots).
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"setAt","parameters":["3","7"]}\n' \
  "$RPC" "$WALLET" "$contract" >"$cfg"
set_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$set_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$set_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"sum4"}\n' \
  "$RPC" "$WALLET" "$contract" >"$cfg"
sum_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$sum_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==7, d' <<<"$sum_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"xs_3"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
value="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$value" == "7" ]] || { echo "FAIL: expected xs_3=7, got $value" >&2; exit 1; }

echo "xrpl-alphanet-tab: ok contract=$contract xs_3=7"
