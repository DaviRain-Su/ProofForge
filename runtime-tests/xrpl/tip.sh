#!/usr/bin/env bash
# Local 2.6.1: Pay.emitToCallerDrops 384 to the caller.
# Funded first-install Create. Public AlphaNet pokeEmit is still -196.
# Not Sdk.Payments. Missing docker/node → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-tip: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-tip: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-http://127.0.0.1:15005}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-tip: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-tip: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
if [[ "$nid" == "21337" ]]; then
  echo "xrpl-tip: skip: public AlphaNet still tefBAD_AUTH -196" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-tip: $RPC $info" >&2

# Same wasm hash + values-only Create is temMALFORMED after the first install.
bash "$here/local-alphanet.sh" down
bash "$here/local-alphanet.sh" up
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
info="$(node "$here/alphanet-rpc.js" info "$cfg")"
echo "xrpl-tip: restarted $info" >&2

echo "xrpl-tip: building XrplTip.wasm (Bedrock/get_* names)" >&2
lake exe pf -- build --target xrpl --out "$root/build/xrpl" XrplTip
wasm="$root/build/xrpl/XrplTip.wasm"
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

ping_out="$(call_fn ping)"
echo "$ping_out" >&2
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$ping_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$ping_out")"
if [[ "$result" != "tesSUCCESS" || "$code" != "0" ]]; then
  echo "FAIL: ping want tesSUCCESS/0 got $result/$code" >&2
  rm -f "$cfg"
  exit 1
fi

rm -f "$cfg"
echo "xrpl-tip: ok contract=$contract ping tesSUCCESS/0 (local emitPayDrops 384; not Sdk.Payments)"
