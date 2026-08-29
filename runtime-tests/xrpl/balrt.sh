#!/usr/bin/env bash
# Live AlphaNet: stamp caller's AccountRoot.Balance (drops) into JSON.
# Genesis account is expected to hold 1e14 drops (100M XRP).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-balrt: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-balrt: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
# Live AccountRoot.Balance in drops, compared after stamp.

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-balrt: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-balrt: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-balrt: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplBalRt.wasm"
if [[ ! -f "$wasm" ]]; then
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplBalRt
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

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

stamp_out="$(call_fn stamp)"
echo "$stamp_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$stamp_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"drops"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
drops="$(node "$here/alphanet-rpc.js" slot "$cfg")"
info_bal="$(node -e '
const https=require("https");
const body=JSON.stringify({method:"account_info",params:[{account:process.argv[1],ledger_index:"validated"}]});
const req=https.request("https://alphanet.xrpl.org",{method:"POST",headers:{"Content-Type":"application/json","Content-Length":Buffer.byteLength(body)}},res=>{let d="";res.on("data",c=>d+=c);res.on("end",()=>{const j=JSON.parse(d);process.stdout.write(String(j.result.account_data.Balance));});});
req.write(body);req.end();
' "$OWNER")"
rm -f "$cfg"
[[ "$drops" == "$info_bal" ]] || {
  echo "FAIL: stamped drops=$drops account_info Balance=$info_bal" >&2
  exit 1
}

echo "xrpl-alphanet-balrt: ok contract=$contract drops=$drops"
