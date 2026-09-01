#!/usr/bin/env bash
# Probe AlphaNet AccountRoot Sequence / Flags / OwnerCount.
# Same host path as Balance (accountroot_id + cache_le + le_field).
# RPC down → skip. Missing import / trap → fail closed. Not Sdk.Account.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-probe-root: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-probe-root: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-root: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-probe-root: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-probe-root: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-probe-root: $RPC $info" >&2

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-root.wasm"
"$wat2wasm" "$here/fixture/probe-root.wat" -o "$wasm"

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: ContractCreate rejected AccountRoot UInt32 le_field" >&2
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
  node "$here/alphanet-rpc.js" call "$cfg"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

poke_out="$(call_fn poke || true)"
echo "$poke_out" >&2
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$poke_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$poke_out")"
if [[ "$result" != "tesSUCCESS" || "$code" != "0" ]]; then
  echo "FAIL: poke did not read Sequence/Flags/OwnerCount (result=$result code=$code)" >&2
  rm -f "$cfg"
  exit 1
fi

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
want_seq="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["result"]["account_data"]["Sequence"])' <<<"$info_json")"
want_flags="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["result"]["account_data"].get("Flags") or 0)' <<<"$info_json")"
want_ownc="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["result"]["account_data"].get("OwnerCount") or 0)' <<<"$info_json")"
rm -f "$cfg"
echo "xrpl-probe-root: seq=$seq flags=$flags ownc=$ownc account_info Sequence=$want_seq Flags=$want_flags OwnerCount=$want_ownc" >&2
[[ "$seq" == "$want_seq" ]] || {
  echo "FAIL: stamped seq=$seq account_info Sequence=$want_seq" >&2
  exit 1
}
# cache_le snapshots AccountRoot before set_data_object_field creates
# ContractData, which increments OwnerCount. Off-by-one is expected.
if [[ "$ownc" != "$want_ownc" && "$((ownc + 1))" != "$want_ownc" ]]; then
  echo "FAIL: stamped ownc=$ownc account_info OwnerCount=$want_ownc" >&2
  exit 1
fi

echo "xrpl-probe-root: ok contract=$contract seq=$seq flags=$flags ownc=$ownc"
