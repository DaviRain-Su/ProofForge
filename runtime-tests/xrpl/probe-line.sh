#!/usr/bin/env bash
# Probe AlphaNet trustline_id. Not Sdk.Trustline.
# Missing import → ContractCreate fail. RPC down → skip.
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

mkdir -p "$root/build/xrpl-alphanet"
wasm="$root/build/xrpl-alphanet/probe-line.wasm"
if ! "$wat2wasm" "$here/fixture/probe-line.wat" -o "$wasm"; then
  echo "FAIL: wat2wasm probe-line" >&2
  exit 1
fi

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
if ! deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"; then
  echo "FAIL: ContractCreate rejected trustline_id import (host not registered)" >&2
  echo "$deploy_out" >&2
  rm -f "$cfg"
  exit 1
fi
echo "$deploy_out" >&2
contract="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAccount"])' <<<"$deploy_out")"

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
  "$RPC" "$WALLET" "$contract" "initialize" >"$cfg"
init_out="$(node "$here/alphanet-rpc.js" call "$cfg")"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","contract_account":"%s","function_name":"%s"}\n' \
  "$RPC" "$WALLET" "$contract" "poke" >"$cfg"
poke_out="$(node "$here/alphanet-rpc.js" call "$cfg" || true)"
echo "$poke_out" >&2
rm -f "$cfg"
code="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("vmReturnCode"))' <<<"$poke_out")"
result="$("$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); print(d.get("result") or d.get("engine_result"))' <<<"$poke_out")"
if [[ "$result" == "tesSUCCESS" ]]; then
  :
elif [[ "$result" == "tecBYTECODE_REJECTED" && "$code" != "None" && -n "$code" ]]; then
  :
else
  echo "FAIL: trustline_id poke did not run ($result code=$code)" >&2
  exit 1
fi
echo "xrpl-probe-line: trustline_id(zero) result=$result vmReturnCode=$code (host exists; not Sdk.Trustline)"
echo "xrpl-probe-line: ok contract=$contract"
