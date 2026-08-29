#!/usr/bin/env bash
# EvmVecStack: permissionless bounded UInt64 LIFO over the StorageVec persistent vector policy
# (capacity 3). Covers seeded construction, push-to-full, CapExceeded, LIFO pop with observable
# return values, empty-pop typed error, clear, and documented stale-slot behavior.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-vec-stack
bin="$root/build/evm/EvmVecStack.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18573}" "$root/build/evm/anvil-vec-stack.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"

solana_lean_require_storage "$addr" 0 7 "constructor seed items[0]"
solana_lean_require_storage "$addr" 1 0 "constructor zero items[1]"
solana_lean_require_storage "$addr" 2 0 "constructor zero items[2]"
solana_lean_require_storage "$addr" 3 1 "constructor depth"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'depthOf()(uint64)')" 1 \
  "depth getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 7 \
  "top view on seed"

# Permissionless pushes fill the active prefix.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'push(uint64)' 8 >/dev/null
solana_lean_require_storage "$addr" 1 8 "push writes items[1]"
solana_lean_require_storage "$addr" 3 2 "push bumps depth"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'push(uint64)' 9 >/dev/null
solana_lean_require_storage "$addr" 2 9 "push writes items[2]"
solana_lean_require_storage "$addr" 3 3 "full stack depth"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 9 \
  "top view on full stack"

# The fourth push reverts CapExceeded() and stores nothing.
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64)' 10)" "full stack push"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'push(uint64)' 10 >/dev/null 2>&1; then
  echo "FAIL: full-stack push unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 3 "full push holds depth"
solana_lean_require_storage "$addr" 0 7 "full push holds items[0]"

# eth_call observes pop's return value without mutating; the real pop then shrinks depth and
# leaves the popped slot stale.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'pop()(uint64)')" 9 \
  "pop returns the top value"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'pop()' >/dev/null
solana_lean_require_storage "$addr" 3 2 "pop shrinks depth"
solana_lean_require_storage "$addr" 2 9 "popped slot stays stale and unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 8 \
  "top view after pop"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'pop()' >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'pop()' >/dev/null
solana_lean_require_storage "$addr" 3 0 "empty stack depth"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 0 \
  "top view on empty stack"

# Empty pop reverts with the typed empty() error and stores nothing.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'pop()')" 'empty()' "empty pop"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pop()' >/dev/null 2>&1; then
  echo "FAIL: empty pop unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 0 "empty pop holds depth"

# Pushes after emptying reuse the stale backing slots.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'push(uint64)' 42 >/dev/null
solana_lean_require_storage "$addr" 0 42 "push after empty overwrites items[0]"
solana_lean_require_storage "$addr" 1 8 "stale items[1] stays unreachable"
solana_lean_require_storage "$addr" 3 1 "depth after re-push"

# clearAll resets only the depth; backing slots stay stale.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'push(uint64)' 43 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'clearAll()' >/dev/null
solana_lean_require_storage "$addr" 3 0 "clearAll clears depth"
solana_lean_require_storage "$addr" 0 42 "clearAll leaves stale items[0] unreachable"
solana_lean_require_storage "$addr" 1 43 "clearAll leaves stale items[1] unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 0 \
  "top view after clear"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'pop()')" 'empty()' "pop after clear"

# Inject an impossible depth and prove no mutation silently repairs malformed persistent state.
solana_lean_set_storage_word "$addr" 3 4
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'topOf()(uint64)')" 0 \
  "malformed depth closes top view"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'push(uint64)' 44)" 'malformed()' "malformed push"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'pop()')" 'malformed()' "malformed pop"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'clearAll()')" 'malformed()' "malformed clear"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'clearAll()' >/dev/null 2>&1; then
  echo "FAIL: malformed clear unexpectedly repaired depth" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 4 "malformed mutations hold depth"
solana_lean_require_storage "$addr" 0 42 "malformed mutations hold items[0]"

echo "evm-anvil-vec-stack: ok (bounded LIFO push/pop/clear + full/empty/malformed failure + stale slots; engineering only)"
