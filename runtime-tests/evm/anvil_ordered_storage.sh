#!/usr/bin/env bash
# Ordered static UInt64 store: immediate write, CALL sandwich, and transactional rollback.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ordered-storage
bin="$root/build/evm/EvmOrderedStorage.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18565}" "$root/build/evm/anvil-ordered-storage.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
recipient="0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC"

solana_lean_require_storage "$addr" 0 1 "constructor status"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'writeNow(uint64)(uint64)' 7)" \
  7 "immediate write return"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'writeNow(uint64)' 7 >/dev/null
solana_lean_require_storage "$addr" 0 7 "immediate write persists without final State update"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'writeNow(uint64)' 1 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'writeAroundSend(address,uint256)' "$recipient" 0 >/dev/null
solana_lean_require_storage "$addr" 0 1 "store/CALL/store restores status"

# A failed value CALL reverts the preceding entered write as part of the EVM transaction.
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'writeAroundSend(address,uint256)' "$recipient" 1 >/dev/null 2>&1; then
  echo "FAIL: unfunded ordered send unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 1 "failed CALL rolls back entered status"

echo "evm-anvil-ordered-storage: ok (immediate write/CALL/restore/rollback; engineering only)"
