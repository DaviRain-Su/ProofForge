#!/usr/bin/env bash
# Local 2.6.1: shared supp on the contract AccountID card via gated vault: pause + storeSelf + emitToCaller.
# Funded first-install Create. Public AlphaNet pokeSelf is still -22.
# Not Sdk.Map. Missing docker/node → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-fund: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-fund: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-http://127.0.0.1:15005}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"
WALLET_B="${XRPL_ALPHANET_WALLET_B:-sp8y8kecNjy88BZRr9U991iiRzFNf}"
OWNER_B="${XRPL_ALPHANET_OWNER_B:-rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-fund: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-fund: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
if [[ "$nid" == "21337" ]]; then
  echo "xrpl-fund: skip: public AlphaNet still -22 / -196" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-fund: $RPC $info" >&2

# Same wasm hash + values-only Create is temMALFORMED after the first install.
bash "$here/local-alphanet.sh" down
bash "$here/local-alphanet.sh" up
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
info="$(node "$here/alphanet-rpc.js" info "$cfg")"
echo "xrpl-fund: restarted $info" >&2

echo "xrpl-fund: building XrplFund.wasm (Bedrock/get_* names)" >&2
lake exe pf -- build --target xrpl --out "$root/build/xrpl" XrplFund
wasm="$root/build/xrpl/XrplFund.wasm"
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","send_amount_drops":"2000000000"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: funded Create rejected" >&2
  rm -f "$cfg"
  exit 1
fi
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount" >&2
  exit 1
}

call_fn() {
  local fn="$1"
  local seed="${2:-$WALLET}"
  local out err
  printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$seed" "$contract" "$fn" >"$cfg"
  err="$(mktemp)"
  set +e
  out="$(node "$here/alphanet-rpc.js" call "$cfg" 2>"$err")"
  set -e
  if [[ -n "$out" ]]; then
    printf '%s\n' "$out"
  else
    printf '{"success":false,"result":"error","engine_result":"error","vmReturnCode":null,"error":%s}\n' \
      "$("$python" -I -S -c 'import json,sys; print(json.dumps(sys.stdin.read()[-400:]))' <"$err")"
  fi
  rm -f "$err"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

printf '{"rpc_url":"%s","wallet_seed":"%s","destination":"%s","drops":"20000000"}\n' \
  "$RPC" "$WALLET" "$OWNER_B" >"$cfg"
node "$here/alphanet-rpc.js" pay "$cfg" >/dev/null

want() {
  local out="$1" code="$2" label="$3"
  echo "$out" >&2
  "$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==int(sys.argv[1]), d' "$code" <<<"$out" \
    || { echo "FAIL: $label want tesSUCCESS/$code got $out" >&2; exit 1; }
}

slot() {
  local owner="$1" key="$2"
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"%s"}\n' \
    "$RPC" "$owner" "$contract" "$key" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg" || echo missing
}

# B cannot pause before grantOp.
denied="$(call_fn pause "$WALLET_B")"
want "$denied" 3 denied-pause

grant="$(call_fn grantOp)"
want "$grant" 0 grantOp

b_pause="$(call_fn pause "$WALLET_B")"
want "$b_pause" 0 b-pause
held="$(call_fn credit)"
want "$held" 4 paused-credit
b_unpause="$(call_fn unpause "$WALLET_B")"
want "$b_unpause" 0 b-unpause

want "$(call_fn credit)" 0 credit
want "$(call_fn credit)" 0 credit
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: A bal want 10" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "10" ]] || { echo "FAIL: supp want 10" >&2; exit 1; }

cap="$(call_fn setCap10)"
want "$cap" 0 setCap10
over="$(call_fn credit)"
want "$over" 1 over-cap
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: cap must keep A=10" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "10" ]] || { echo "FAIL: cap must keep supp=10" >&2; exit 1; }

want "$(call_fn sendToB)" 0 sendToB
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: after send A=5" >&2; exit 1; }
[[ "$(slot "$OWNER_B" bal)" == "5" ]] || { echo "FAIL: after send B=5" >&2; exit 1; }

printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
before="$(node "$here/alphanet-rpc.js" balance "$cfg")"
want "$(call_fn cashToB)" 0 cashToB
[[ "$(slot "$OWNER" bal)" == "0" ]] || { echo "FAIL: after cash A=0" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "5" ]] || { echo "FAIL: after cash supp=5" >&2; exit 1; }
printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
after="$(node "$here/alphanet-rpc.js" balance "$cfg")"
rm -f "$cfg"
delta="$("$python" -I -S -c 'import sys; print(int(sys.argv[2])-int(sys.argv[1]))' "$before" "$after")"
[[ "$delta" == "192" ]] || { echo "FAIL: B XRP delta want 192 got $delta" >&2; exit 1; }

echo "xrpl-fund: ok contract=$contract cap=10 op-pause A=0 B.points=5 supp=5 B.xrp+=192 (not Sdk.Payments)"
