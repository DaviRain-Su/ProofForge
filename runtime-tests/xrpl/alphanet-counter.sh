#!/usr/bin/env bash
# Live AlphaNet gate for parameterized Counter.
# Create Function ABI + increment(1); do NOT call initialize (UINT64 init
# knocks 3.3.0 offline even with ABI). Missing RPC → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-counter: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-counter: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-counter: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-counter: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-counter: $RPC $info" >&2

echo "xrpl-alphanet-counter: building Counter.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" Counter
wasm="$root/build/xrpl-alphanet/Counter.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }
# Existing Counter.wasm source on AlphaNet may lack initialize ABI.
# Do not reinstall with a different ABI (temMALFORMED / HTTP 502).
printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"increment":1,"decrement":1,"divide":1,"modulo":1,"scale":1}}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount: $deploy_out" >&2
  exit 1
}

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"increment","parameters":["1"]}\n' \
  "$RPC" "$WALLET" "$contract" >"$cfg"
inc_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$inc_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$inc_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"get"}\n' \
  "$RPC" "$WALLET" "$contract" >"$cfg"
get_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$get_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$get_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"value"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
value="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1, got $value" >&2; exit 1; }

echo "xrpl-alphanet-counter: ok contract=$contract value=1"
