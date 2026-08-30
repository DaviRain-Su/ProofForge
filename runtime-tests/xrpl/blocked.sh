#!/usr/bin/env bash
# Re-probe the three node-blocked surfaces against a local SmartContract
# standalone (transia/alphanet / dangell/smart-contracts). Not public 21337.
# Does not open Sdk.Payments / Sdk.Map. Missing docker/node → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-blocked: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-blocked: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-blocked: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-http://127.0.0.1:15005}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

if [[ "$RPC" == http://127.0.0.1:* || "$RPC" == http://localhost:* ]]; then
  # First ContractCreate of a wasm can carry InstanceParameterValues.
  # A later Create of the same hash with values against a source that
  # stored no ParameterType ABI is temMALFORMED. Restart so emit is first.
  bash "$here/local-alphanet.sh" down
  bash "$here/local-alphanet.sh" up
fi

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-blocked: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
ver="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin).get("build_version"))' <<<"$info")"
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-blocked: skip: SmartContract not enabled ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-blocked: $RPC nid=$nid version=$ver $info" >&2

mkdir -p "$root/build/xrpl-alphanet"

deploy() {
  local wasm="$1"
  local extra="${2:-}"
  printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s"%s}\n' \
    "$RPC" "$WALLET" "$wasm" "$extra" >"$cfg"
  node "$here/alphanet-rpc.js" deploy "$cfg"
}

call_fn() {
  local contract="$1"
  local fn="$2"
  local params="${3:-}"
  local out err
  if [[ -n "$params" ]]; then
    printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s","parameters":%s}\n' \
      "$RPC" "$WALLET" "$contract" "$fn" "$params" >"$cfg"
  else
    printf '{"rpc_url":"%s","wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
      "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  fi
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

# Local 2.6.1-rc1 uses get_* names. Public 3.3.0-rc1 probes stay in probe-*.wat.
# --- 1. emit Payment ---
emit_wasm="$root/build/xrpl-alphanet/probe-emit-local.wasm"
"$wat2wasm" "$here/fixture/probe-emit-local.wat" -o "$emit_wasm"
echo "xrpl-blocked: deploy emit with tfSendAmount values (no ParameterType ABI)" >&2
set +e
fund_err="$(mktemp)"
emit_deploy="$(deploy "$emit_wasm" ',"send_amount_drops":"2000000000"' 2>"$fund_err")"
fund_rc=$?
set -e
if [[ $fund_rc -ne 0 ]]; then
  echo "xrpl-blocked: funded Create rejected" >&2
  cat "$fund_err" >&2 || true
  fund_status=rejected
  echo "FAIL: local emit needs first-install InstanceParameterValues" >&2
  exit 1
else
  fund_status=ok
fi
rm -f "$fund_err"
echo "$emit_deploy" >&2
emit_c="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$emit_deploy")"
emit_bal="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin).get("contractBalance"))' <<<"$emit_deploy")"
echo "xrpl-blocked: contract $emit_c balance=$emit_bal" >&2
init_out="$(call_fn "$emit_c" initialize)"
echo "initialize $init_out" >&2
build_out="$(call_fn "$emit_c" pokeBuild)"
echo "pokeBuild $build_out" >&2
emit_out="$(call_fn "$emit_c" pokeEmit)"
echo "pokeEmit $emit_out" >&2
emit_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$emit_out")"
emit_result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$emit_out")"

# --- 2. ContractData owner ---
owner_wasm="$root/build/xrpl-alphanet/probe-owner-local.wasm"
"$wat2wasm" "$here/fixture/probe-owner-local.wat" -o "$owner_wasm"
echo "xrpl-blocked: deploy owner probe" >&2
caller_code=missing
self_code=missing
sle_owner_code=missing
if owner_deploy="$(deploy "$owner_wasm")"; then
  echo "$owner_deploy" >&2
  owner_c="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$owner_deploy")"
  call_fn "$owner_c" initialize >/dev/null
  caller_out="$(call_fn "$owner_c" pokeCaller)"
  echo "pokeCaller $caller_out" >&2
  self_out="$(call_fn "$owner_c" pokeSelf)"
  echo "pokeSelf $self_out" >&2
  owner_out="$(call_fn "$owner_c" pokeOwner)"
  echo "pokeOwner $owner_out" >&2
  caller_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$caller_out")"
  self_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$self_out")"
  sle_owner_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$owner_out")"
else
  echo "xrpl-blocked: owner deploy rejected" >&2
fi

# --- 3. Parameters ---
# 2.6.1 node `sign` of Function.ParameterType → temBAD_SIGNATURE / temMALFORMED.
# Public 3.3.0: Create ABI + Call values is tesSUCCESS (probe-param). Skip here.
if [[ "$nid" == "21337" ]]; then
  param_wasm="$root/build/xrpl-alphanet/probe-param-local.wasm"
  "$wat2wasm" "$here/fixture/probe-param-local.wat" -o "$param_wasm"
  echo "xrpl-blocked: deploy param probe with bump ABI" >&2
  printf '{"rpc_url":"%s","wallet_seed":"%s","wasm_path":"%s","function_params":{"bump":1}}\n' \
    "$RPC" "$WALLET" "$param_wasm" >"$cfg"
  if param_deploy="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
    echo "$param_deploy" >&2
    param_c="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$param_deploy")"
    call_fn "$param_c" initialize >/dev/null
    param_out="$(call_fn "$param_c" bump '["1"]')"
    echo "bump Parameters $param_out" >&2
    param_result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result") or "none")' <<<"$param_out")"
    param_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$param_out")"
  else
    echo "xrpl-blocked: param deploy rejected" >&2
    param_result=rejected
    param_code=missing
  fi
else
  echo "xrpl-blocked: skip Parameters on nid=$nid (2.6.1 cannot sign Function.ParameterType)" >&2
  param_result="skip-local-sign"
  param_code="n/a"
fi

rm -f "$cfg"

echo "xrpl-blocked: summary nid=$nid version=$ver"
echo "  emit Payment: $emit_result/$emit_code (tesSUCCESS/0 = green)"
echo "  Create tfSendAmount: $fund_status"
echo "  write caller card: $caller_code (0 = green)"
echo "  write contract card 524313: $self_code (0 = green, -17/-22 = still blocked)"
echo "  write sfOwner 524290: ${sle_owner_code:-missing}"
echo "  ContractCall Parameters: $param_result/$param_code (tesSUCCESS = green; 502 public; SIGSEGV local 2.6.1)"
echo "xrpl-blocked: ok (probe recorded; Sdk.Payments/Map still closed unless emit+self+params are all green)"
