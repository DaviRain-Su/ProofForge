#!/usr/bin/env bash
# Live AlphaNet: owner-gated mint + anyone-can-pay points.
# A mint(5); B mint(1) → unauthorized; A pay(B,2) → A=3 B=2.
# `supp` on the minter card tracks total supply; pay does not change it.
# Not XRP, not Sdk.Map. Missing RPC → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-mint: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-mint: skip: node not found" >&2
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
  echo "xrpl-alphanet-mint: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-mint: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-mint: $RPC $info" >&2

echo "xrpl-alphanet-mint: building XrplMint.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplMint
wasm="$root/build/xrpl-alphanet/XrplMint.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"mint":1,"mintTo":4,"pay":4,"burn":1,"setCap":1,"approve":1,"takeFrom":4}}\n' \
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

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mint","parameters":["5"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
mint_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$mint_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$mint_out"

# B is not the compile-time minter.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mint","parameters":["1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
deny_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$deny_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$deny_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","2"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
pay_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pay_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pay_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
supp_b="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
rm -f "$cfg"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A bal want 3 got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "2" ]] || { echo "FAIL: B bal want 2 got $bal_b" >&2; exit 1; }
[[ "$supp_a" == "5" ]] || { echo "FAIL: A supp want 5 after mint+pay, got $supp_a" >&2; exit 1; }
[[ "$supp_b" == "missing" || "$supp_b" == "0" ]] || { echo "FAIL: B supp should stay missing/0, got $supp_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pause"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
pause_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pause_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mint","parameters":["1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
paused_mint="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$paused_mint" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$paused_mint"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
paused_pay="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$paused_pay" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$paused_pay"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mintTo","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
paused_mto="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$paused_mto" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$paused_mto"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a2="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b2="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$bal_a2" == "3" ]] || { echo "FAIL: A bal should stay 3 while paused, got $bal_a2" >&2; exit 1; }
[[ "$bal_b2" == "2" ]] || { echo "FAIL: B bal should stay 2 while paused, got $bal_b2" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"unpause"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
unpause_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$unpause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unpause_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
resume_pay="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$resume_pay" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$resume_pay"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a3="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b3="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a3" == "2" ]] || { echo "FAIL: A bal want 2 after unpause pay, got $bal_a3" >&2; exit 1; }
[[ "$bal_b3" == "3" ]] || { echo "FAIL: B bal want 3 after unpause pay, got $bal_b3" >&2; exit 1; }

# B is not the minter: pause/unpause unauthorized; halt stays 0 on A's card.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pause"}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
b_pause="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$b_pause" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$b_pause"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"unpause"}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
b_unpause="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$b_unpause" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$b_unpause"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"halt"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
halt_a="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"halt"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
halt_b="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a4="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b4="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$halt_a" == "0" || "$halt_a" == "missing" ]] || { echo "FAIL: A halt want 0/missing after B pause, got $halt_a" >&2; exit 1; }
[[ "$halt_b" == "missing" || "$halt_b" == "0" ]] || { echo "FAIL: B halt should not be paused, got $halt_b" >&2; exit 1; }
[[ "$bal_a4" == "2" ]] || { echo "FAIL: A bal want 2 after B pause, got $bal_a4" >&2; exit 1; }
[[ "$bal_b4" == "3" ]] || { echo "FAIL: B bal want 3 after B pause, got $bal_b4" >&2; exit 1; }

# mintTo: minter credits B's card directly. B mintTo is unauthorized.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mintTo","parameters":["%s","%s","%s","4"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
mto="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$mto" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$mto"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mintTo","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
mto_deny="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$mto_deny" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$mto_deny"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a5="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b5="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a5" == "2" ]] || { echo "FAIL: A bal want 2 after mintTo, got $bal_a5" >&2; exit 1; }
[[ "$bal_b5" == "7" ]] || { echo "FAIL: B bal want 7 after mintTo, got $bal_b5" >&2; exit 1; }

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a5="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$supp_a5" == "9" ]] || { echo "FAIL: A supp want 9 after mintTo, got $supp_a5" >&2; exit 1; }

# Supply overflow: mintTo more than u64Max - supp → status 1, cards stay.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mintTo","parameters":["%s","%s","%s","18446744073709551615"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
ov_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$ov_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$ov_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a6="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b6="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a6="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a6" == "2" ]] || { echo "FAIL: A bal want 2 after supp overflow, got $bal_a6" >&2; exit 1; }
[[ "$bal_b6" == "7" ]] || { echo "FAIL: B bal want 7 after supp overflow, got $bal_b6" >&2; exit 1; }
[[ "$supp_a6" == "9" ]] || { echo "FAIL: A supp want 9 after supp overflow, got $supp_a6" >&2; exit 1; }

# Burn 1 from A. Underflow burn(9) is a no-op. Pause blocks burn.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"burn","parameters":["1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
burn_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$burn_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$burn_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"burn","parameters":["9"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
under_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$under_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$under_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a7="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$bal_a7" == "1" ]] || { echo "FAIL: A bal want 1 after burn, got $bal_a7" >&2; exit 1; }

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a7="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$supp_a7" == "8" ]] || { echo "FAIL: A supp want 8 after burn, got $supp_a7" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pause"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
pause2="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pause2" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pause2"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"burn","parameters":["1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
paused_burn="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$paused_burn" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$paused_burn"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a8="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b8="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a8" == "1" ]] || { echo "FAIL: A bal want 1 after paused burn, got $bal_a8" >&2; exit 1; }
[[ "$bal_b8" == "7" ]] || { echo "FAIL: B bal want 7 after paused burn, got $bal_b8" >&2; exit 1; }

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a8="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$supp_a8" == "8" ]] || { echo "FAIL: A supp want 8 after paused burn, got $supp_a8" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"unpause"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
unpause2="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$unpause2" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unpause2"

# Cap: missing/0 is unlimited. setCap(8) with supp=8 blocks mint; setCap(9) allows mint(1).
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"setCap","parameters":["8"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
cap8="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$cap8" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$cap8"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mint","parameters":["1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
cap_mint="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$cap_mint" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$cap_mint"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"setCap","parameters":["9"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
cap9="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$cap9" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$cap9"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"mint","parameters":["1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
cap_ok="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$cap_ok" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$cap_ok"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"setCap","parameters":["1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
b_cap="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$b_cap" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$b_cap"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a9="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
supp_a9="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"cap"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
cap_a="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"cap"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
cap_b="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
rm -f "$cfg"
[[ "$bal_a9" == "2" ]] || { echo "FAIL: A bal want 2 after cap mint, got $bal_a9" >&2; exit 1; }
[[ "$supp_a9" == "9" ]] || { echo "FAIL: A supp want 9 after cap mint, got $supp_a9" >&2; exit 1; }
[[ "$cap_a" == "9" ]] || { echo "FAIL: A cap want 9, got $cap_a" >&2; exit 1; }
[[ "$cap_b" == "missing" || "$cap_b" == "0" ]] || { echo "FAIL: B cap should stay missing/0, got $cap_b" >&2; exit 1; }

SRC_W0="4887904824787662773"
SRC_W1="17928715436519199904"
SRC_W2="3895982578"

# Allowance: A grants allw=2 to compile-time spender B. A cannot takeFrom.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"approve","parameters":["2"]}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
appr="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$appr" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$appr"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"takeFrom","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
a_take="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$a_take" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==3, d' <<<"$a_take"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"takeFrom","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
b_take="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$b_take" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$b_take"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"takeFrom","parameters":["%s","%s","%s","9"]}\n' \
  "$RPC" "$WALLET_B" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
under_take="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$under_take" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$under_take"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a10="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b10="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"allw"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
allw_a="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"allw"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
allw_b="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
rm -f "$cfg"
[[ "$bal_a10" == "1" ]] || { echo "FAIL: A bal want 1 after takeFrom, got $bal_a10" >&2; exit 1; }
[[ "$bal_b10" == "8" ]] || { echo "FAIL: B bal want 8 after takeFrom, got $bal_b10" >&2; exit 1; }
[[ "$allw_a" == "1" ]] || { echo "FAIL: A allw want 1 after takeFrom, got $allw_a" >&2; exit 1; }
[[ "$allw_b" == "missing" || "$allw_b" == "0" ]] || { echo "FAIL: B allw should stay missing/0, got $allw_b" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pause"}\n' \
  "$RPC" "$WALLET_A" "$contract" >"$cfg"
pause3="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$pause3" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pause3"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"takeFrom","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
paused_take="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$paused_take" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$paused_take"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a11="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b11="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a11" == "1" ]] || { echo "FAIL: A bal want 1 after paused takeFrom, got $bal_a11" >&2; exit 1; }
[[ "$bal_b11" == "8" ]] || { echo "FAIL: B bal want 8 after paused takeFrom, got $bal_b11" >&2; exit 1; }

echo "xrpl-alphanet-mint: ok contract=$contract A.bal=1 B.bal=8 allw=1"
