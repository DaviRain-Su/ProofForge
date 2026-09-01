#!/usr/bin/env bash
# Dual-backend Anvil gate: Counter behavior with solc vs yulc bytecode (E-B3 seed).
# Missing anvil/cast/yulc → skip (exit 0). Bytecode may differ; storage behavior must match.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-counter
solana_lean_yulc_or_skip evm-anvil-yulc-counter

out="$root/build/evm-yulc-anvil"
solana_lean_dual_build_program Counter "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-counter

solana_lean_start_anvil "${PF_EVM_PORT:-18590}" "$root/build/evm/anvil-yulc-counter.log"

run_counter_suite() {
  local label="$1" bytecode="$2"
  local addr
  addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    7 "$label: constructor view"
  solana_lean_require_storage "$addr" 0 7 "$label: constructor storage"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'increment(uint64)' 5 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    12 "$label: post-increment view"
  solana_lean_require_storage "$addr" 0 12 "$label: post-increment storage"
  echo "$addr"
}

solc_addr="$(run_counter_suite solc "$SOLC_HEX")"
yulc_addr="$(run_counter_suite yulc "$YULC_HEX")"

# Cross-check both contracts reached the same logical state.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'get()(uint64)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'get()(uint64)')" \
  "solc vs yulc final get() mismatch"

echo "evm-anvil-yulc-counter: ok (dual-backend behavior match; engineering only)"
