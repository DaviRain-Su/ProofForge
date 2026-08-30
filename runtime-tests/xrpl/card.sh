#!/usr/bin/env bash
# Live AlphaNet: Sdk.Card names over caller-card freeze/pay.
# A credit(5) pay(B,2) → A=3 B=2; A freeze then pay → status 5, cards stay.
# Dest freeze also blocks incoming pay. Not XRP, not Sdk.Map, not global halt.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-card: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-card: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET_A="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER_A="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"
DEST_W0="2252104427062869200"
DEST_W1="15364824358342992452"
DEST_W2="1353963993"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-card: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-card: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-card: $RPC $info" >&2

echo "xrpl-alphanet-card: building XrplCard.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplCard
wasm="$root/build/xrpl-alphanet/XrplCard.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"credit":1,"pay":4}}\n' \
  "$RPC" "$WALLET_A" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount" >&2
  exit 1
}

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","destination":"%s","drops":"20000000"}\n' \
  "$RPC" "$WALLET_A" "$OWNER_B" >"$cfg"
node "$here/alphanet-rpc.js" pay "$cfg" >/dev/null 2>&1 || true

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"initialize"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
init_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"credit","parameters":["5"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
credit_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$credit_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$credit_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","2"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
pay_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pay_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pay_out"

slot() {
  local owner="$1" key="$2"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"%s"}\n' \
    "$RPC" "$owner" "$contract" "$key" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg"
}

bal_a="$(slot "$OWNER_A" bal)"
bal_b="$(slot "$OWNER_B" bal)"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A bal want 3 got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "2" ]] || { echo "FAIL: B bal want 2 got $bal_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"freeze"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
fr_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$fr_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$fr_out"
lock_a="$(slot "$OWNER_A" lock)"
[[ "$lock_a" == "1" ]] || { echo "FAIL: A lock want 1 got $lock_a" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
frozen_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$frozen_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==5, d' <<<"$frozen_out"
bal_a="$(slot "$OWNER_A" bal)"
bal_b="$(slot "$OWNER_B" bal)"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A bal should stay 3 while frozen, got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "2" ]] || { echo "FAIL: B bal should stay 2 while A frozen, got $bal_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"unfreeze"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
un_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$un_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$un_out"
lock_a="$(slot "$OWNER_A" lock)"
[[ "$lock_a" == "0" ]] || { echo "FAIL: A lock want 0 after unfreeze got $lock_a" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
pay2_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pay2_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pay2_out"
bal_a="$(slot "$OWNER_A" bal)"
bal_b="$(slot "$OWNER_B" bal)"
[[ "$bal_a" == "2" ]] || { echo "FAIL: A bal want 2 after unfreeze pay, got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "3" ]] || { echo "FAIL: B bal want 3 after unfreeze pay, got $bal_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"freeze"}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
frb_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$frb_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$frb_out"
lock_b="$(slot "$OWNER_B" lock)"
[[ "$lock_b" == "1" ]] || { echo "FAIL: B lock want 1 got $lock_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
destfr_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$destfr_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==5, d' <<<"$destfr_out"
bal_a="$(slot "$OWNER_A" bal)"
bal_b="$(slot "$OWNER_B" bal)"
[[ "$bal_a" == "2" ]] || { echo "FAIL: A bal should stay 2 while dest frozen, got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "3" ]] || { echo "FAIL: B bal should stay 3 while dest frozen, got $bal_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"unfreeze"}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
unb_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$unb_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unb_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
pay3_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pay3_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pay3_out"
bal_a="$(slot "$OWNER_A" bal)"
bal_b="$(slot "$OWNER_B" bal)"
rm -f "$cfg"
[[ "$bal_a" == "1" ]] || { echo "FAIL: A bal want 1 after dest unfreeze pay, got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "4" ]] || { echo "FAIL: B bal want 4 after dest unfreeze pay, got $bal_b" >&2; exit 1; }

echo "xrpl-alphanet-card: ok contract=$contract A.bal=1 B.bal=4 freeze=status5"
