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
  echo "xrpl-safe: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-safe: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-http://127.0.0.1:15005}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-safe: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-safe: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
if [[ "$nid" == "21337" ]]; then
  echo "xrpl-safe: skip: public AlphaNet still -22 / -196" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-safe: $RPC $info" >&2

# Same wasm hash + values-only Create is temMALFORMED after the first install.
bash "$here/local-alphanet.sh" down
bash "$here/local-alphanet.sh" up
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
info="$(node "$here/alphanet-rpc.js" info "$cfg")"
echo "xrpl-safe: restarted $info" >&2

echo "xrpl-safe: building XrplSafe.wasm (Bedrock/get_* names)" >&2
lake exe pf -- build --target xrpl --out "$root/build/xrpl" XrplSafe
wasm="$root/build/xrpl/XrplSafe.wasm"
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

credit_out="$(call_fn credit)"
echo "$credit_out" >&2
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$credit_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$credit_out")"
if [[ "$result" != "tesSUCCESS" || "$code" != "0" ]]; then
  echo "FAIL: credit want tesSUCCESS/0 got $result/$code" >&2
  rm -f "$cfg"
  exit 1
fi

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
bal="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$contract" "$contract" >"$cfg"
supp="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
[[ "$bal" == "5" ]] || { echo "FAIL: after credit caller bal want 5 got $bal" >&2; exit 1; }
[[ "$supp" == "5" ]] || { echo "FAIL: after credit contract supp want 5 got $supp" >&2; exit 1; }

freeze_out="$(call_fn freeze)"
echo "$freeze_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$freeze_out"

frozen_cash="$(call_fn cash)"
echo "$frozen_cash" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==5, d' <<<"$frozen_cash"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
bal="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$bal" == "5" ]] || { echo "FAIL: frozen cash must keep bal=5 got $bal" >&2; exit 1; }

unfreeze_out="$(call_fn unfreeze)"
echo "$unfreeze_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unfreeze_out"

pause_out="$(call_fn pause)"
echo "$pause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pause_out"

held_out="$(call_fn credit)"
echo "$held_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$held_out"

held_cash="$(call_fn cash)"
echo "$held_cash" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$held_cash"

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
bal="$(node "$here/alphanet-rpc.js" slot "$cfg")"
[[ "$bal" == "5" ]] || { echo "FAIL: paused credit must keep bal=5 got $bal" >&2; exit 1; }

unpause_out="$(call_fn unpause)"
echo "$unpause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unpause_out"

cash_out="$(call_fn cash)"
echo "$cash_out" >&2
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$cash_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$cash_out")"
if [[ "$result" != "tesSUCCESS" || "$code" != "0" ]]; then
  echo "FAIL: cash want tesSUCCESS/0 got $result/$code" >&2
  rm -f "$cfg"
  exit 1
fi

printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"bal"}\n' \
  "$RPC" "$OWNER" "$contract" >"$cfg"
bal="$(node "$here/alphanet-rpc.js" slot "$cfg")"
printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"supp"}\n' \
  "$RPC" "$contract" "$contract" >"$cfg"
supp="$(node "$here/alphanet-rpc.js" slot "$cfg" || echo missing)"
rm -f "$cfg"
[[ "$bal" == "0" ]] || { echo "FAIL: after cash caller bal want 0 got $bal" >&2; exit 1; }
[[ "$supp" == "0" ]] || { echo "FAIL: after cash contract supp want 0 got $supp" >&2; exit 1; }

echo "xrpl-safe: ok contract=$contract freeze=5 pause=4 then cash (bal=0 supp=0 emit 192; not Sdk.Payments)"
