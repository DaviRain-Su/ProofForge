#!/usr/bin/env bash
# Live AlphaNet gate: per-caller ContractData cards (XLS-0101 user shards).
# Wallet A credits twice → A's bal=2. Wallet B credits once → B's bal=1, A stays 2.
# That is multi-user by Owner, not a single vault. Missing RPC → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-bal: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-bal: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET_A="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER_A="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
# Same secp256k1 fixture as Bedrock own.sh. Funded from genesis on AlphaNet.
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-bal: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-bal: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-bal: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplBal.wasm"
if [[ ! -f "$wasm" ]]; then
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplBal
fi

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET_A" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"

call_as() {
  local seed="$1" fn="$2"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$seed" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg"
}

slot_as() {
  local owner="$1"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
    "$RPC" "$owner" "$contract" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg" || echo "missing"
}

init_out="$(call_as "$WALLET_A" initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

credit_a1="$(call_as "$WALLET_A" credit)"
echo "$credit_a1" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("vmReturnCode")==0, d' <<<"$credit_a1"
credit_a2="$(call_as "$WALLET_A" credit)"
echo "$credit_a2" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("vmReturnCode")==0, d' <<<"$credit_a2"
bal_a="$(slot_as "$OWNER_A")"
[[ "$bal_a" == "2" ]] || { echo "FAIL: A bal want 2 got $bal_a" >&2; exit 1; }

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","destination":"%s","drops":"20000000"}\n' \
  "$RPC" "$WALLET_A" "$OWNER_B" >"$cfg"
if ! pay_out="$(node "$here/alphanet-rpc.js" pay "$cfg")"; then
  echo "xrpl-alphanet-bal: skip: cannot fund second wallet $OWNER_B" >&2
  rm -f "$cfg"
  echo "xrpl-alphanet-bal: partial ok contract=$contract A=2 (B unfunded)"
  exit 0
fi
echo "$pay_out" >&2

credit_b="$(call_as "$WALLET_B" credit)"
echo "$credit_b" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$credit_b"
bal_b="$(slot_as "$OWNER_B")"
bal_a2="$(slot_as "$OWNER_A")"
rm -f "$cfg"
[[ "$bal_b" == "1" ]] || { echo "FAIL: B bal want 1 got $bal_b" >&2; exit 1; }
[[ "$bal_a2" == "2" ]] || { echo "FAIL: A bal should stay 2, got $bal_a2" >&2; exit 1; }

echo "xrpl-alphanet-bal: ok contract=$contract A=$OWNER_A bal=2 B=$OWNER_B bal=1"
