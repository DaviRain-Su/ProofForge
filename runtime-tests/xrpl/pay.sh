#!/usr/bin/env bash
# Live AlphaNet: internal points transfer across two caller cards.
# A credit(5) then pay(B, 2) → A.bal=3 B.bal=2. Not XRP, not Sdk.Map.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-pay: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-pay: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET_A="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER_A="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"
# Little-endian limbs of d0bc2a540b15411f44a24dfb58d23ad5d9d9b350 (B).
DEST_W0="2252104427062869200"
DEST_W1="15364824358342992452"
DEST_W2="1353963993"
# Little-endian limbs of b5f762798a53d543a014caf8b297cff8f2f937e8 (A / genesis).
SRC_W0="4887904824787662773"
SRC_W1="17928715436519199904"
SRC_W2="3895982578"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-pay: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-pay: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-pay: $RPC $info" >&2

echo "xrpl-alphanet-pay: building XrplPay.wasm" >&2
lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplPay
wasm="$root/build/xrpl-alphanet/XrplPay.wasm"
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

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A bal want 3 got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "2" ]] || { echo "FAIL: B bal want 2 got $bal_b" >&2; exit 1; }

# Underflow: pay(B, 9) while A has 3 → status 1, cards unchanged.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","9"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
under_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$under_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$under_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a2="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b2="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a2" == "3" ]] || { echo "FAIL: A bal should stay 3 after underflow, got $bal_a2" >&2; exit 1; }
[[ "$bal_b2" == "2" ]] || { echo "FAIL: B bal should stay 2 after underflow, got $bal_b2" >&2; exit 1; }

# Reverse: B pay(A, 1) → A=4 B=1. Second wallet initiates.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_B" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
rev_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$rev_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$rev_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a3="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b3="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a3" == "4" ]] || { echo "FAIL: A bal want 4 after reverse, got $bal_a3" >&2; exit 1; }
[[ "$bal_b3" == "1" ]] || { echo "FAIL: B bal want 1 after reverse, got $bal_b3" >&2; exit 1; }

# Self-pay: A pay(A, 1) is alias-safe. Flush then credit the same card → A stays 4, B stays 1.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$SRC_W0" "$SRC_W1" "$SRC_W2" >"$cfg"
self_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$self_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$self_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a4="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b4="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a4" == "4" ]] || { echo "FAIL: A bal want 4 after self-pay, got $bal_a4" >&2; exit 1; }
[[ "$bal_b4" == "1" ]] || { echo "FAIL: B bal want 1 after self-pay, got $bal_b4" >&2; exit 1; }

# Dest overflow: B credit(u64Max-1) → B=max; A pay(B,1) → status 1, A stays 4.
printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"credit","parameters":["18446744073709551614"]}\n' \
  "$RPC" "$WALLET_B" "$contract" >"$cfg"
cap_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$cap_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$cap_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"pay","parameters":["%s","%s","%s","1"]}\n' \
  "$RPC" "$WALLET_A" "$contract" "$DEST_W0" "$DEST_W1" "$DEST_W2" >"$cfg"
ov_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$ov_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==1, d' <<<"$ov_out"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_A" "$contract" >"$cfg"
bal_a5="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER_B" "$contract" >"$cfg"
bal_b5="$(node "$here/alphanet-rpc.js" slot "$cfg")"
rm -f "$cfg"
[[ "$bal_a5" == "4" ]] || { echo "FAIL: A bal should stay 4 after dest overflow, got $bal_a5" >&2; exit 1; }
[[ "$bal_b5" == "18446744073709551615" ]] || { echo "FAIL: B bal want u64Max after cap, got $bal_b5" >&2; exit 1; }

echo "xrpl-alphanet-pay: ok contract=$contract A.bal=4 B.bal=max dest-overflow-noop"
