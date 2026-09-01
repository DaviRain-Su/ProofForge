#!/usr/bin/env bash
# Live AlphaNet engineering gate for zero-parameter XrplHold (Ownable + Pausable).
# Public RPC 502s ContractCall with Parameters; this program has none.
# Sequence: initialize → bump (value=1) → pause → bump (vmReturnCode=4, value stays 1)
#           → unpause → bump (value=2).
# Missing node / unfunded wallet / RPC down → skip (exit 0), not pass.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet-hold: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet-hold: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
WALLET="${XRPL_ALPHANET_WALLET:-snoPBrXtMeMyMHUVTgbuqAfg1SUTb}"
OWNER="${XRPL_ALPHANET_OWNER:-rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh}"

cfg="$(mktemp)"
printf '{"rpc_url":"%s"}\n' "$RPC" >"$cfg"
if ! info="$(node "$here/alphanet-rpc.js" info "$cfg")"; then
  echo "xrpl-alphanet-hold: skip: cannot reach $RPC" >&2
  rm -f "$cfg"
  exit 0
fi
nid="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["network_id"])' <<<"$info")"
smart="$("$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["smart_contract"])' <<<"$info")"
if [[ "$nid" != "21337" || "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet-hold: skip: not AlphaNet SmartContract ($info)" >&2
  rm -f "$cfg"
  exit 0
fi
echo "xrpl-alphanet-hold: $RPC $info" >&2

wasm="$root/build/xrpl-alphanet/XrplHold.wasm"
if [[ ! -f "$wasm" ]]; then
  echo "xrpl-alphanet-hold: building XrplHold.wasm" >&2
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" XrplHold
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

printf '{"rpc_url":"%s","network_id":21337,"wallet_seed":"%s","wasm_path":"%s"}\n' \
  "$RPC" "$WALLET" "$wasm" >"$cfg"
deploy_out="$(node "$here/alphanet-rpc.js" deploy "$cfg")"
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
  node "$here/alphanet-rpc.js" call "$cfg"
}

slot_value() {
  printf '{"rpc_url":"%s","owner":"%s","contract_account":"%s","key":"value"}\n' \
    "$RPC" "$OWNER" "$contract" >"$cfg"
  node "$here/alphanet-rpc.js" slot "$cfg"
}

init_out="$(call_fn initialize)"
echo "$init_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$init_out"

bump_out="$(call_fn bump)"
echo "$bump_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$bump_out"
value="$(slot_value)"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1 after bump, got $value" >&2; exit 1; }

pause_out="$(call_fn pause)"
echo "$pause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$pause_out"

held_out="$(call_fn bump)"
echo "$held_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==4, d' <<<"$held_out"
value="$(slot_value)"
[[ "$value" == "1" ]] || { echo "FAIL: expected value=1 after paused bump, got $value" >&2; exit 1; }

unpause_out="$(call_fn unpause)"
echo "$unpause_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$unpause_out"

resume_out="$(call_fn bump)"
echo "$resume_out" >&2
"$python" -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d.get("result")=="tesSUCCESS" and d.get("vmReturnCode")==0, d' <<<"$resume_out"
value="$(slot_value)"
rm -f "$cfg"
[[ "$value" == "2" ]] || { echo "FAIL: expected value=2 after unpause bump, got $value" >&2; exit 1; }

echo "xrpl-alphanet-hold: ok contract=$contract value=2 paused=4"
