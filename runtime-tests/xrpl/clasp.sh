#!/usr/bin/env bash
# Local 2.6.1: freeze-gated dual timelock. Frozen cancel/cashB return 5.
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
  echo "xrpl-clasp: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-clasp: skip: node not found" >&2
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
  echo "xrpl-clasp: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-clasp: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
if [[ "$nid" == "21337" ]]; then
  echo "xrpl-clasp: skip: public AlphaNet still -22 / -196" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-clasp: $RPC $info" >&2

# Same wasm hash + values-only Create is temMALFORMED after the first install.
bash "$here/local-alphanet.sh" down
bash "$here/local-alphanet.sh" up
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
info="$(node "$here/alphanet-rpc.js" info "$cfg")"
echo "xrpl-clasp: restarted $info" >&2

echo "xrpl-clasp: building XrplClasp.wasm (Bedrock/get_* names)" >&2
lake exe pf -- build --target xrpl --out "$root/build/xrpl" XrplClasp
wasm="$root/build/xrpl/XrplClasp.wasm"
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

want "$(call_fn credit)" 0 credit
want "$(call_fn credit)" 0 credit
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: A bal want 10" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "10" ]] || { echo "FAIL: supp want 10" >&2; exit 1; }

want "$(call_fn pause "$WALLET_B")" 3 b-pause-ungranted
want "$(call_fn grantOp)" 0 grantOp
want "$(call_fn pause "$WALLET_B")" 0 b-pause
want "$(call_fn lockIn)" 4 paused-lockIn
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: pause must keep A=10" >&2; exit 1; }
want "$(call_fn unpause)" 0 unpause

want "$(call_fn lockIn)" 0 lockIn
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: after lockIn A want 5" >&2; exit 1; }
[[ "$(slot "$contract" esc)" == "5" ]] || { echo "FAIL: after lockIn esc want 5" >&2; exit 1; }

want "$(call_fn freeze)" 0 freeze
want "$(call_fn cancel)" 5 frozen-cancel
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: freeze must keep A=5" >&2; exit 1; }
want "$(call_fn unfreeze)" 0 unfreeze

want "$(call_fn cancel)" 0 cancel
[[ "$(slot "$OWNER" bal)" == "10" ]] || { echo "FAIL: after cancel A want 10" >&2; exit 1; }
[[ "$(slot "$contract" esc)" == "0" ]] || { echo "FAIL: after cancel esc want 0" >&2; exit 1; }

want "$(call_fn lockIn)" 0 lockIn2
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: after lockIn2 A want 5" >&2; exit 1; }

want "$(call_fn freeze "$WALLET_B")" 0 freeze-b
want "$(call_fn cashB "$WALLET_B")" 5 frozen-cash
[[ "$(slot "$contract" esc)" == "5" ]] || { echo "FAIL: frozen B cash must keep esc=5" >&2; exit 1; }
want "$(call_fn unfreeze "$WALLET_B")" 0 unfreeze-b

want "$(call_fn cashB "$WALLET_B")" 1 too-early
[[ "$(slot "$contract" esc)" == "5" ]] || { echo "FAIL: early B cash must keep esc=5" >&2; exit 1; }

want "$(call_fn cashB)" 3 a-cash
[[ "$(slot "$contract" esc)" == "5" ]] || { echo "FAIL: A cash must keep esc=5" >&2; exit 1; }

want "$(call_fn cancel)" 1 cancel-late
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: late cancel must keep A=5" >&2; exit 1; }

printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
before="$(node "$here/alphanet-rpc.js" balance "$cfg")"
want "$(call_fn cashB "$WALLET_B")" 0 cashB
[[ "$(slot "$contract" esc)" == "0" ]] || { echo "FAIL: after cash esc want 0" >&2; exit 1; }
[[ "$(slot "$contract" supp)" == "5" ]] || { echo "FAIL: after cash supp want 5" >&2; exit 1; }
[[ "$(slot "$OWNER" bal)" == "5" ]] || { echo "FAIL: cash must keep A=5" >&2; exit 1; }
printf '{"rpc_url":"%s","account":"%s"}\n' "$RPC" "$OWNER_B" >"$cfg"
after="$(node "$here/alphanet-rpc.js" balance "$cfg")"
rm -f "$cfg"
# ContractCall Fee is 1_000_000 drops; emit pays 192 to B (the caller of cashB).
got="$("$python" -I -S -c 'import sys; print(int(sys.argv[2])-int(sys.argv[1])+1000000)' "$before" "$after")"
[[ "$got" == "192" ]] || { echo "FAIL: B XRP net-of-fee want 192 got $got (before=$before after=$after)" >&2; exit 1; }

echo "xrpl-clasp: ok contract=$contract freeze cancel=5 then B cashB +192-fee (not Sdk.Payments)"
