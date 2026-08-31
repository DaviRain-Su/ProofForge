#!/usr/bin/env bash
# Probe AlphaNet RippleState read path: trustline_id + cache_le + le_field.
# Not Sdk.Trustline. Missing import → ContractCreate fail. RPC down → skip.
# Prereq: fund holder B if unfunded, then TrustSet USD/issuer B from genesis;
# TrustSet failure fails the script. Missing SLE (negative vmReturnCode)
# still means the path ran (-10 is not balance 0).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-probe-line: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-probe-line: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-line: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"
LINE_CURRENCY="${XRPL_ALPHANET_LINE_CURRENCY:-USD}"
LINE_LIMIT="${XRPL_ALPHANET_LINE_LIMIT:-1000000}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-probe-line: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-probe-line: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-probe-line: $RPC $info" >&2

# Holder B needs its own reserve: a zero-balance account cannot TrustSet.
printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
b_balance="$(node "$here/alphanet-rpc.js" balance "$cfg" 2>/dev/null || echo 0)"
if [[ "$b_balance" == "0" ]]; then
  echo "xrpl-probe-line: funding $OWNER_B with 400 XRP" >&2
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","destination":"%s","drops":"400000000"}\n' \
    "$RPC" "$WALLET" "$OWNER_B" >"$cfg"
  node "$here/alphanet-rpc.js" pay "$cfg" >&2 || {
    echo "FAIL: could not fund $OWNER_B" >&2
    rm -f "$cfg"
    exit 1
  }
fi

# Genesis is the holder, B the compile-time issuer in probe-line.wat.
# No RippleState → no SLE → -10; the trust line must land before the poke.
printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","issuer":"%s","currency":"%s","value":"%s"}\n' \
  "$RPC" "$WALLET" "$OWNER_B" "$LINE_CURRENCY" "$LINE_LIMIT" >"$cfg"
if ! trust_out="$(node "$here/alphanet-rpc.js" trustset "$cfg")"; then
  echo "FAIL: TrustSet $LINE_CURRENCY/$OWNER_B did not land" >&2
  echo "${trust_out:-}" >&2
  rm -f "$cfg"
  exit 1
fi
echo "xrpl-probe-line: trustset $trust_out" >&2

# Peer view of the line: counterparty is the holder (genesis).
printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","account":"%s","issuer":"%s","currency":"%s"}\n' \
  "$RPC" "$WALLET_B" "$OWNER_B" "$OWNER" "$LINE_CURRENCY" >"$cfg"
if ! line_out="$(node "$here/alphanet-rpc.js" line "$cfg")"; then
  echo "FAIL: no RippleState $LINE_CURRENCY line between genesis $OWNER and $OWNER_B" >&2
  rm -f "$cfg"
  exit 1
fi
rm -f "$cfg"
echo "xrpl-probe-line: RippleState $line_out" >&2

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-line.wasm"
if ! "$wat2wasm" "$here/fixture/probe-line.wat" -o "$wasm"; then
  echo "FAIL: wat2wasm probe-line" >&2
  rm -f "$cfg"
  exit 1
fi

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: ContractCreate rejected trustline_id/cache_le/le_field import" >&2
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
rm -f "$cfg"
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$poke_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$poke_out")"
if [[ "$result" == "tesSUCCESS" ]]; then
  # ContractData owner is the caller (genesis), not the trust line holder.
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"drops"}\n' \
    "$RPC" "$OWNER" "$contract" >"$cfg"
  drops="$(node "$here/alphanet-rpc.js" slot "$cfg")"
  rm -f "$cfg"
  echo "xrpl-probe-line: drops_slot=$drops" >&2
elif [[ "$result" == "tecBYTECODE_REJECTED" && "$code" =~ ^-?[0-9]+$ ]]; then
  :
else
  echo "FAIL: RippleState poke did not run ($result code=$code)" >&2
  exit 1
fi
echo "xrpl-probe-line: engine_result=$result vmReturnCode=$code (trustline_id+cache_le+le_field host probe; not Sdk.Trustline)"
if [[ "$result" == "tesSUCCESS" && -n "${drops:-}" && "$drops" != "0" ]]; then
  echo "xrpl-probe-line: balance STAmount prefix=0x$(printf '%016x' "$drops")"
  echo "xrpl-probe-line: ok contract=$contract drops=$drops"
else
  echo "xrpl-probe-line: ok contract=$contract"
fi
