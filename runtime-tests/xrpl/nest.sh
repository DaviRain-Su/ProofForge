#!/usr/bin/env bash
# Live AlphaNet: nested JSON slot user_bal → {user:{bal}} per caller.
# Wallet A credit(3) → A's user.bal=3. Wallet B credit(5) → B's user.bal=5, A stays 3.
# Nested JSON, not a Map. Missing RPC → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-nest: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-nest: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET_A="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER_A="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-nest: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-nest: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-nest: $RPC $info" >&2

echo "xrpl-alphanet-nest: building XrplNest.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplNest
wasm="$root/build/xrpl-alphanet/XrplNest.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"credit":1}}\n' \
  "$RPC" "$WALLET_A" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount" >&2
  exit 1
}

call_as() {
  local seed="$1" fn="$2"
  shift 2
  if [[ $# -eq 0 ]]; then
    printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
      "$RPC" "$seed" "$contract" "$fn" >"$cfg"
  else
    local params="["
    local first=1
    for a in "$@"; do
      if [[ $first -eq 1 ]]; then first=0; else params+=","; fi
      params+="\"$a\""
    done
    params+="]"
    printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s","parameters":%s}\n' \
      "$RPC" "$seed" "$contract" "$fn" "$params" >"$cfg"
  fi
  node "$here/alphanet-rpc.js" call "$cfg"
}

slot_as() {
  local owner="$1"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"user_bal"}\n' \
    "$RPC" "$owner" "$contract" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg" || echo "missing"
}

init_out="$(call_as "$WALLET_A" initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

credit_a="$(call_as "$WALLET_A" credit 3)"
echo "$credit_a" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$credit_a"
bal_a="$(slot_as "$OWNER_A")"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A nested user.bal want 3 got $bal_a" >&2; exit 1; }

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","destination":"%s","drops":"20000000"}\n' \
  "$RPC" "$WALLET_A" "$OWNER_B" >"$cfg"
if ! pay_out="$(node "$here/alphanet-rpc.js" pay "$cfg")"; then
  echo "xrpl-alphanet-nest: skip: cannot fund second wallet $OWNER_B" >&2
  rm -f "$cfg"
  echo "xrpl-alphanet-nest: partial ok contract=$contract A=3 (B unfunded)"
  exit 0
fi
echo "$pay_out" >&2

credit_b="$(call_as "$WALLET_B" credit 5)"
echo "$credit_b" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$credit_b"
bal_b="$(slot_as "$OWNER_B")"
bal_a2="$(slot_as "$OWNER_A")"
rm -f "$cfg"
[[ "$bal_b" == "5" ]] || { echo "FAIL: B nested user.bal want 5 got $bal_b" >&2; exit 1; }
[[ "$bal_a2" == "3" ]] || { echo "FAIL: A nested user.bal should stay 3, got $bal_a2" >&2; exit 1; }

echo "xrpl-alphanet-nest: ok contract=$contract A=$OWNER_A user.bal=3 B=$OWNER_B user.bal=5"
