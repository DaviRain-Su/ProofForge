#!/usr/bin/env bash
# Probe AlphaNet host_lib.build_txn / add_txn_field / emit_built_txn.
# Not XLS-0101 narrative submitTransaction. Not Sdk.Payments / Sdk.Amm.
# Missing import → ContractCreate fail (exit 1). RPC down → skip (exit 0).
# pokeBuild returning any wasm i32 means the builder host exists.
# pokeEmit tesSUCCESS is the only green light for a Runtime Payment leaf.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-probe-emit: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-probe-emit: skip: node not found" >&2
  exit 0
fi
wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-emit: skip: wat2wasm not found" >&2
  exit 0
}

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-probe-emit: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-probe-emit: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-probe-emit: $RPC $info" >&2

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-emit.wasm"
"$wat2wasm" "$here/fixture/probe-emit.wat" -o "$wasm"
[[ -f "$wasm" ]] || { echo "FAIL: wat2wasm did not write $wasm" >&2; exit 1; }

# AlphaNet 3.3.0-rc1: InstanceParameters on ContractCreate is temMALFORMED,
# so Create-time tfSendAmount cannot fund the pseudo-account. Deploy bare.
printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: ContractCreate rejected build_txn/add_txn_field/emit_built_txn (host not registered)" >&2
  echo "$deploy_out" >&2
  rm -f "$cfg"
  exit 1
fi
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"
[[ -n "$contract" && "$contract" != "None" && "$contract" != "null" ]] || {
  echo "FAIL: deploy did not return contractAccount: $deploy_out" >&2
  exit 1
}

call_fn() {
  local fn="$1"
  printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
    "$RPC" "$WALLET" "$contract" "$fn" >"$cfg"
  node "$here/alphanet-rpc.js" call "$cfg" || true
}

init_out="$(call_fn initialize)"
echo "initialize $init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

build_out="$(call_fn pokeBuild)"
echo "pokeBuild $build_out" >&2
build_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$build_out")"
build_result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$build_out")"
# Host exists if wasm ran: tesSUCCESS (builder index ≥ 0) or a host error code.
if [[ "$build_result" == "tesSUCCESS" ]]; then
  :
elif [[ "$build_result" == "tecBYTECODE_REJECTED" && "$build_code" != "None" && "$build_code" != "null" && -n "$build_code" ]]; then
  :
else
  echo "FAIL: pokeBuild did not run ($build_result code=$build_code)" >&2
  rm -f "$cfg"
  exit 1
fi
echo "xrpl-probe-emit: pokeBuild result=$build_result vmReturnCode=$build_code (builder host exists)" >&2

emit_out="$(call_fn pokeEmit)"
echo "pokeEmit $emit_out" >&2
rm -f "$cfg"
emit_code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$emit_out")"
emit_result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$emit_out")"
echo "xrpl-probe-emit: pokeEmit result=$emit_result vmReturnCode=$emit_code" >&2
if [[ "$emit_result" == "tesSUCCESS" && "$emit_code" == "0" ]]; then
  echo "xrpl-probe-emit: ok contract=$contract emit=green (192 drops Payment). Still not Sdk.Payments."
  exit 0
fi
# Host ran but Payment did not land. -196 = tecPSEUDO_ACCOUNT on this build.
# Do not open a Runtime leaf / Sdk.Payments.
echo "xrpl-probe-emit: ok contract=$contract build=$build_result/$build_code emit=$emit_result/$emit_code (host exists; Payment not green)"
