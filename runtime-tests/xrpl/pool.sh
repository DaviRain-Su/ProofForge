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
  echo "xrpl-pool: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-pool: skip: node not found" >&2
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
  echo "xrpl-pool: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-pool: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
if [[ "$nid" == "21337" ]]; then
  echo "xrpl-pool: skip: public AlphaNet still -22 / -196" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-pool: $RPC $info" >&2

# Same wasm hash + values-only Create is temMALFORMED after the first install.
bash "$here/local-alphanet.sh" down
bash "$here/local-alphanet.sh" up
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
info="$(node "$here/alphanet-rpc.js" info "$cfg")"
echo "xrpl-pool: restarted $info" >&2

echo "xrpl-pool: building XrplPool.wasm (Bedrock/get_* names)" >&2
lake exe pf -- build --target xrpl --out "$root/build/xrpl" XrplPool
wasm="$root/build/xrpl/XrplPool.wasm"
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
  local out err
  printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
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

# Activate B on a fresh local ledger.
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

credit_out="$(call_fn credit)"
want "$credit_out" 0 credit
credit_out="$(call_fn credit)"
want "$credit_out" 0 credit
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: A bal want 10" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "10" ]] || { echo "FAIL: supp want 10" >&2; exit 1; }

send_out="$(call_fn sendToB)"
want "$send_out" 0 sendToB
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: after send A bal want 5" >&2; exit 1; }
[[ "$(slot "$OWNER_B" bal)" == "5" ]] || { echo "FAIL: after send B bal want 5" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "10" ]] || { echo "FAIL: after send supp want 10" >&2; exit 1; }

freeze_out="$(call_fn freeze)"
want "$freeze_out" 0 freeze
frozen="$(call_fn sendToB)"
want "$frozen" 5 frozen-send
frozen_cash="$(call_fn cashToB)"
want "$frozen_cash" 5 frozen-cash
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: frozen must keep A=5" >&2; exit 1; }

unfreeze_out="$(call_fn unfreeze)"
want "$unfreeze_out" 0 unfreeze

pause_out="$(call_fn pause)"
want "$pause_out" 0 pause
held="$(call_fn credit)"
want "$held" 4 paused-credit
held_send="$(call_fn sendToB)"
want "$held_send" 4 paused-send
held_cash="$(call_fn cashToB)"
want "$held_cash" 4 paused-cash
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: paused must keep A=5" >&2; exit 1; }

unpause_out="$(call_fn unpause)"
want "$unpause_out" 0 unpause

printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
before="$(node "$here/alphanet-rpc.js" balance "$cfg")"

cash_out="$(call_fn cashToB)"
want "$cash_out" 0 cashToB
[[ "$(slot "$OWNER" bal)" == "0" ]] || { echo "FAIL: after cash A bal want 0" >&2; exit 1; }
[[ "$(slot "$OWNER_B" bal)" == "5" ]] || { echo "FAIL: after cash B points want 5" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "5" ]] || { echo "FAIL: after cash supp want 5" >&2; exit 1; }

printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
after="$(node "$here/alphanet-rpc.js" balance "$cfg")"
rm -f "$cfg"
delta="$("$python" -I -S -c 'import sys; print(int(sys.argv[2])-int(sys.argv[1]))' "$before" "$after")"
[[ "$delta" == "192" ]] || { echo "FAIL: B XRP delta want 192 got $delta (before=$before after=$after)" >&2; exit 1; }

echo "xrpl-pool: ok contract=$contract A=0 B.points=5 supp=5 B.xrp+=192 (not Sdk.Payments)"
