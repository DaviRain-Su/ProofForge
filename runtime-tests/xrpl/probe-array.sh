#!/usr/bin/env bash
# Probe Bedrock host set/get_data_array_element_field. Not a ProofForge digest gate.
# Missing docker/bedrock → skip. Instantiation or negative host code → fail closed.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

xrpl_init xrpl-probe-array

wat2wasm="$(xrpl_find_tool wat2wasm)" || {
  echo "xrpl-probe-array: skip: wat2wasm not found" >&2
  exit 0
}

fixture="$here/fixture"
wat="$fixture/probe-array.wat"
wasm="$root/build/xrpl/probe-array.wasm"
staged="$fixture/contract/target/wasm32-unknown-unknown/release/Counter.wasm"

mkdir -p "$(dirname "$wasm")"
"$wat2wasm" "$wat" -o "$wasm"
[[ -f "$wasm" ]] || { echo "FAIL: wat2wasm did not write $wasm" >&2; exit 1; }

mkdir -p "$(dirname "$staged")"
cp -f "$wasm" "$staged"
mkdir -p "$fixture/.bedrock/node-config"
rm -rf "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/xrpld.cfg" "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/genesis.json" "$fixture/.bedrock/node-config/genesis.json"

cleanup() {
  if [[ -n "${bedrock:-}" ]]; then
    (cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
  fi
}
trap cleanup EXIT

echo "xrpl-probe-array: starting local node" >&2
(cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
(cd "$fixture" && "$bedrock" node start)

wallet="$(xrpl_genesis_seed)"
owner="$(xrpl_genesis_address)"

deploy_out="$(cd "$fixture" && "$bedrock" deploy \
  --network local \
  --skip-build \
  --skip-abi \
  --abi abi.json \
  --wallet "$wallet")" || {
  echo "FAIL: deploy (wasm likely rejected array import): $deploy_out" >&2
  exit 1
}
echo "$deploy_out" >&2

contract="$(xrpl_field "$deploy_out" "Contract Account")"
[[ -n "$contract" ]] || {
  echo "FAIL: deploy did not return Contract Account: $deploy_out" >&2
  exit 1
}

xrpl_call() {
  local fn="$1"
  local params="{}"
  if [[ -n "${2:-}" ]]; then
    params="$2"
  fi
  local cfg
  cfg="$(mktemp)"
  XRPL_CFG="$cfg" \
  XRPL_CONTRACT="$contract" XRPL_FN="$fn" XRPL_WALLET="$wallet" \
    XRPL_ABI="$fixture/abi.json" XRPL_PARAMS="$params" \
    "$python" -I -S -c '
import json, os
json.dump({
    "contract_account": os.environ["XRPL_CONTRACT"],
    "function_name": os.environ["XRPL_FN"],
    "network_url": "ws://localhost:6006",
    "wallet_seed": os.environ["XRPL_WALLET"],
    "abi_path": os.environ["XRPL_ABI"],
    "parameters": json.loads(os.environ.get("XRPL_PARAMS") or "{}"),
}, open(os.environ["XRPL_CFG"], "w", encoding="utf-8"))
'
  local out
  out="$(node "$here/call.js" "$cfg")"
  rm -f "$cfg"
  printf '%s\n' "$out"
}

xrpl_call_code() {
  "$python" -I -S -c 'import json,sys; print(json.load(sys.stdin).get("returnCode"))' <<<"$1"
}

init_out="$(xrpl_call initialize '{"initial_value":"0"}')"
xrpl_require_equal "$(xrpl_call_code "$init_out")" "0" "initialize status"

poke_out="$(xrpl_call poke '{}')"
echo "xrpl-probe-array: poke $poke_out" >&2
xrpl_require_equal "$(xrpl_call_code "$poke_out")" "0" "poke status"

host_code="$(xrpl_slot_u64 "$owner" "$contract" "value")"
echo "xrpl-probe-array: set_data_array_element_field returned $host_code" >&2

"$python" -I -S -c '
import json, sys, urllib.request
owner, contract, host_code = sys.argv[1], sys.argv[2], int(sys.argv[3])
req = urllib.request.Request(
    "http://localhost:5005",
    data=json.dumps({
        "method": "account_objects",
        "params": [{"account": owner, "ledger_index": "validated"}],
    }).encode(),
    headers={"Content-Type": "application/json"},
)
result = json.load(urllib.request.urlopen(req, timeout=10))["result"]
found = None
for obj in result.get("account_objects") or []:
    if obj.get("LedgerEntryType") != "ContractData":
        continue
    if obj.get("ContractAccount") != contract:
        continue
    found = obj.get("ContractJson") or {}
    break
if found is None:
    raise SystemExit("missing ContractData")
print(json.dumps(found, indent=2, sort_keys=True))
if host_code != 0:
    # i32 negative host codes are stored as the low 16 bits of the unsigned slot.
    print("xrpl-probe-array: FAIL host code", host_code, file=sys.stderr)
    raise SystemExit("array host rejected the write")
if "xs" not in found:
    raise SystemExit("array key xs missing from ContractJson")
print("xrpl-probe-array: xs present")
' "$owner" "$contract" "$host_code"

echo "xrpl-probe-array: FAIL: set_data_array_element_field traps (tecWASM_REJECTED)" >&2
exit 1
