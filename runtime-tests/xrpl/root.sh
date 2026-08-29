#!/usr/bin/env bash
# Live AlphaNet: stamp caller's AccountRoot Sequence / Flags / OwnerCount.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-root: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-root: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-root: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-root: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-root: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplRoot.wasm"
if [[ ! -f "$wasm" ]]; then
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplRoot
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

slot_of() {
  local key="$1"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"%s"}\n' \
    "$RPC" "$OWNER" "$contract" "$key" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg"
}

seq="$(slot_of seq)"
flags="$(slot_of flags)"
ownc="$(slot_of ownc)"
info_json="$(node -e '
const https=require("https");
const body=JSON.stringify({method:"account_info",params:[{account:process.argv[1],ledger_index:"validated"}]});
const req=https.request("https://alphanet.xrpl.org",{method:"POST",headers:{"Content-Type":"application/json","Content-Length":Buffer.byteLength(body),"User-Agent":"ProofForge"}},res=>{let d="";res.on("data",c=>d+=c);res.on("end",()=>process.stdout.write(d));});
req.write(body);req.end();
' "$OWNER")"
rm -f "$cfg"
want_seq="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["result"]["account_data"]["Sequence"])' <<<"$info_json")"
want_ownc="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["result"]["account_data"].get("OwnerCount") or 0)' <<<"$info_json")"
[[ "$seq" == "$want_seq" ]] || {
  echo "FAIL: stamped seq=$seq account_info Sequence=$want_seq" >&2
  exit 1
}
if [[ "$ownc" != "$want_ownc" && "$((ownc + 1))" != "$want_ownc" ]]; then
  echo "FAIL: stamped ownc=$ownc account_info OwnerCount=$want_ownc" >&2
  exit 1
fi

echo "xrpl-alphanet-root: ok contract=$contract seq=$seq flags=$flags ownc=$ownc"
