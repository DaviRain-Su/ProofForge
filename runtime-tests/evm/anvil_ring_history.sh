#!/usr/bin/env bash
# EvmRingHistory: permissionless dequeue/clear/reuse UInt64 event history over the StorageRing
# persistent circular-buffer policy (capacity 3). Covers seeded construction, append-to-full with
# a typed full() error, FIFO advance across the wrap boundary, canonical head reset on empty,
# typed empty() advance, reset with documented stale slots, wraparound slot reuse, and fail-closed
# malformed head/live metadata.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ring-history
bin="$root/build/evm/EvmRingHistory.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmRingHistory.bin" >&2
  lake build Examples.EvmRingHistory >/dev/null \
    || { echo "FAIL: lake build Examples.EvmRingHistory failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmRingHistory >/dev/null \
    || { echo "FAIL: build registered EvmRingHistory failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18583}" "$root/build/evm/anvil-ring-history.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmRingHistory.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"

solana_lean_require_storage "$addr" 0 7 "constructor seed tape[0]"
solana_lean_require_storage "$addr" 1 0 "constructor zero tape[1]"
solana_lean_require_storage "$addr" 2 0 "constructor zero tape[2]"
solana_lean_require_storage "$addr" 3 0 "constructor canonical head"
solana_lean_require_storage "$addr" 4 1 "constructor live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'liveOf()(uint64)')" 1 \
  "live getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'headOf()(uint64)')" 0 \
  "head getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 7 \
  "front view on seed"

# Permissionless appends fill the tape; the return value is the physical slot that received the
# event, observed on eth_call without mutating.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'append(uint64)(uint64)' 8)" 1 "append 8 returns the physical tail slot"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 8 >/dev/null
solana_lean_require_storage "$addr" 1 8 "append writes tape[1]"
solana_lean_require_storage "$addr" 4 2 "append bumps live"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 9 >/dev/null
solana_lean_require_storage "$addr" 2 9 "append writes tape[2]"
solana_lean_require_storage "$addr" 4 3 "full tape live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 7 \
  "front view on full tape"

# The fourth append reverts with the typed full() error and stores nothing.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'append(uint64)' 10)" 'full()' "full tape append"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'append(uint64)' 10 >/dev/null 2>&1; then
  echo "FAIL: full-tape append unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 4 3 "full append holds live"
solana_lean_require_storage "$addr" 0 7 "full append holds tape[0]"

# eth_call observes advance's return value without mutating; the real advance then moves the
# head off slot 0 and the next append wraps back to physical slot 0.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'advance()(uint64)')" 7 \
  "advance returns the front event"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'advance()' >/dev/null
solana_lean_require_storage "$addr" 3 1 "advance moves head"
solana_lean_require_storage "$addr" 4 2 "advance shrinks live"
solana_lean_require_storage "$addr" 0 7 "advanced slot stays stale and unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 8 \
  "front view after advance"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'append(uint64)(uint64)' 10)" 0 "wrapped append returns the reused slot 0"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 10 >/dev/null
solana_lean_require_storage "$addr" 0 10 "wrapped append overwrites stale tape[0]"
solana_lean_require_storage "$addr" 4 3 "wrapped append refills live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 8 \
  "front view across the wrap boundary"

# Advancing drains the wrap-extended live order and canonicalizes head back to 0 on empty.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'advance()(uint64)')" 8 \
  "advance 1 returns the wrapped front"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'advance()' >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'advance()' >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'advance()' >/dev/null
solana_lean_require_storage "$addr" 3 0 "emptied advance canonicalizes head"
solana_lean_require_storage "$addr" 4 0 "emptied advance clears live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 0 \
  "front view on emptied tape"

# Empty advance reverts with the typed empty() error and stores nothing.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'advance()')" 'empty()' "empty advance"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'advance()' >/dev/null 2>&1; then
  echo "FAIL: empty advance unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 4 0 "empty advance holds live"

# Appends after emptying reuse the stale backing slots from the canonical empty state.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 42 >/dev/null
solana_lean_require_storage "$addr" 0 42 "append after empty overwrites tape[0]"
solana_lean_require_storage "$addr" 1 8 "stale tape[1] stays unreachable"
solana_lean_require_storage "$addr" 4 1 "live after re-append"

# reset clears only the canonical metadata; backing slots stay stale and unreachable, then the
# next append reuses slot 0.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 43 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'reset()' >/dev/null
solana_lean_require_storage "$addr" 3 0 "reset clears head"
solana_lean_require_storage "$addr" 4 0 "reset clears live"
solana_lean_require_storage "$addr" 0 42 "reset leaves stale tape[0] unreachable"
solana_lean_require_storage "$addr" 1 43 "reset leaves stale tape[1] unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 0 \
  "front view after reset"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'advance()')" 'empty()' "advance after reset"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'append(uint64)' 44 >/dev/null
solana_lean_require_storage "$addr" 0 44 "post-reset append reuses tape[0]"
solana_lean_require_storage "$addr" 4 1 "post-reset live"

# Inject impossible metadata and prove no mutation silently repairs malformed persistent state.
solana_lean_set_storage_word "$addr" 3 3
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 0 \
  "malformed head closes the front view"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'append(uint64)' 45)" 'malformed()' "malformed append"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'advance()')" 'malformed()' "malformed advance"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'reset()')" 'malformed()' "malformed reset"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'reset()' >/dev/null 2>&1; then
  echo "FAIL: malformed reset unexpectedly repaired head" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 3 "malformed mutations hold head"
solana_lean_require_storage "$addr" 4 1 "malformed mutations hold live"

solana_lean_set_storage_word "$addr" 4 4
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'append(uint64)' 45)" 'malformed()' "malformed live append"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'advance()')" 'malformed()' "malformed live advance"
solana_lean_require_storage "$addr" 4 4 "malformed live mutations hold live"

# A masked non-canonical empty state (live 0 with head != 0) fails closed as well.
solana_lean_set_storage_word "$addr" 4 0
solana_lean_set_storage_word "$addr" 3 2
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'currentOf()(uint64)')" 0 \
  "masked empty head closes the front view"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'advance()')" 'malformed()' "masked empty advance"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'reset()')" 'malformed()' "masked empty reset"
solana_lean_require_storage "$addr" 3 2 "masked empty mutations hold head"

echo "evm-anvil-ring-history: ok (drain/clear/reuse ring history append/advance/reset + wraparound + full/empty/malformed + stale slots; engineering only)"
