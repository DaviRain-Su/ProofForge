#!/usr/bin/env bash
# Permissionless capacity-3 bounded UInt64 checkpoints with typed full/unordered/malformed errors.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-checkpoint-trace
bin="$root/build/evm/EvmCheckpointTrace.bin"
if [[ ! -f "$bin" ]]; then
  lake build Examples.EvmCheckpointTrace >/dev/null
  lake exe pf -- build --target evm --out "$root/build/evm" EvmCheckpointTrace >/dev/null
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18687}" "$root/build/evm/anvil-checkpoint-trace.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

for slot in 0 1 2 3 4 5 6; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero trace state"
done

for pair in "5 50" "10 100" "20 200"; do
  key="${pair%% *}"
  value="${pair#* }"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'push(uint64,uint64)(uint64)' "$key" "$value")" "$value" "push returns value"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'push(uint64,uint64)' "$key" "$value" >/dev/null
done
solana_lean_require_storage "$addr" 0 5 "trace key 0"
solana_lean_require_storage "$addr" 1 10 "trace key 1"
solana_lean_require_storage "$addr" 2 20 "trace key 2"
solana_lean_require_storage "$addr" 3 50 "trace value 0"
solana_lean_require_storage "$addr" 4 100 "trace value 1"
solana_lean_require_storage "$addr" 5 200 "trace value 2"
solana_lean_require_storage "$addr" 6 3 "full trace count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'lowerValue(uint64)(uint64)' 6)" 100 "permissionless lower bound"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'latestValue()(uint64)')" 200 \
  "permissionless latest"

# Full growth and decreasing keys remain distinct typed outcomes; same-key overwrite remains
# available without count growth.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64,uint64)' 21 210)" 'full()' "typed full growth"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64,uint64)' 19 190)" 'unordered()' "typed decreasing key"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'push(uint64,uint64)' 20 222 >/dev/null
solana_lean_require_storage "$addr" 5 222 "typed trace latest overwrite"
solana_lean_require_storage "$addr" 6 3 "typed trace overwrite holds count"

# Over-capacity count and duplicate live keys are independently corrupted through
# anvil_setStorageAt and must fail closed before any store.
solana_lean_set_storage_word "$addr" 6 4
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'latestValue()(uint64)')" 0 \
  "malformed count latest fallback"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64,uint64)' 30 300)" 'malformed()' "malformed count push"
solana_lean_require_storage "$addr" 6 4 "malformed count is not repaired"
solana_lean_require_storage "$addr" 5 222 "malformed count holds value"

solana_lean_set_storage_word "$addr" 6 2
solana_lean_set_storage_word "$addr" 1 5
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'lowerValue(uint64)(uint64)' 5)" 0 "duplicate key lower fallback"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64,uint64)' 8 80)" 'malformed()' "duplicate key push"
solana_lean_require_storage "$addr" 1 5 "duplicate key is not repaired"
solana_lean_require_storage "$addr" 6 2 "duplicate key holds count"

echo "evm-anvil-checkpoint-trace: ok (permissionless append/overwrite/latest/lower + typed full/order + corruption; engineering only)"
