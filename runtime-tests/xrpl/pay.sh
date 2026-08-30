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
rm -f "$cfg"
[[ "$bal_a" == "3" ]] || { echo "FAIL: A bal want 3 got $bal_a" >&2; exit 1; }
[[ "$bal_b" == "2" ]] || { echo "FAIL: B bal want 2 got $bal_b" >&2; exit 1; }

echo "xrpl-alphanet-pay: ok contract=$contract A.bal=3 B.bal=2"
