#!/usr/bin/env bash
# EvmRingMailbox: owner-gated reject-at-full UInt64 ring-queue mailbox over the StorageRing
# persistent circular-buffer policy (capacity 4). Covers wraparound delivery/receipt, the
# CapExceeded full gate, Unauthorized, empty take, purge with documented stale slots, and
# fail-closed malformed head/live metadata (including a masked non-canonical empty head).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ring-mailbox
bin="$root/build/evm/EvmRingMailbox.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmRingMailbox.bin" >&2
  lake build Examples.EvmRingMailbox >/dev/null \
    || { echo "FAIL: lake build Examples.EvmRingMailbox failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmRingMailbox >/dev/null \
    || { echo "FAIL: build registered EvmRingMailbox failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18582}" "$root/build/evm/anvil-ring-mailbox.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmRingMailbox.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

admin_words="$("$python" -I -S -c "
b=bytes.fromhex('${sender#0x}')
print(int.from_bytes(b[0:8], 'little'), int.from_bytes(b[8:16], 'little'),
      int.from_bytes(b[16:20], 'little'))
")"
admin_w0="${admin_words%% *}"
rest="${admin_words#* }"
admin_w1="${rest%% *}"
admin_w2="${rest#* }"
solana_lean_require_storage "$addr" 0 "$admin_w0" "constructor admin.w0"
solana_lean_require_storage "$addr" 1 "$admin_w1" "constructor admin.w1"
solana_lean_require_storage "$addr" 2 "$admin_w2" "constructor admin.w2"
for slot in 3 4 5 6; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero pending slot"
done
solana_lean_require_storage "$addr" 7 0 "constructor canonical head"
solana_lean_require_storage "$addr" 8 0 "constructor empty live"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'adminOf()(address)')" \
  "$sender" "admin getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'liveOf()(uint64)')" 0 \
  "empty live getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'headOf()(uint64)')" 0 \
  "canonical head getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 0 \
  "front view on empty mailbox"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 0)" 0 "OOB read on empty mailbox is the 0 fallback"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"

# Non-admin deliver reverts Unauthorized(other) and cannot append.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'deliver(uint64)' 1)" "$other" "non-admin deliver"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'deliver(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-admin deliver unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 8 0 "unauthorized deliver holds live"

# Admin deliveries fill the live ring in order.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 11 >/dev/null
solana_lean_require_storage "$addr" 3 11 "deliver writes pending[0]"
solana_lean_require_storage "$addr" 8 1 "deliver bumps live"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 22 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 1)" 22 "runtime-indexed read 1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 2)" 0 "live-range read fallback 2"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 33 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 2)" 33 "runtime-indexed read 2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 3)" 0 "live-range read fallback 3"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 44 >/dev/null
solana_lean_require_storage "$addr" 6 44 "deliver writes pending[3]"
solana_lean_require_storage "$addr" 8 4 "full mailbox live"
for i in 0 1 2 3; do
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'messageAt(uint64)(uint64)' "$i")" "$(( (i + 1) * 11 ))" "live read $i"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 4)" 0 "OOB read is the 0 fallback on a full mailbox"

# Full mailbox rejects the fifth delivery with CapExceeded() and stores nothing.
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'deliver(uint64)' 55)" "full mailbox deliver"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'deliver(uint64)' 55 >/dev/null 2>&1; then
  echo "FAIL: full-mailbox deliver unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 8 4 "full deliver holds live"
solana_lean_require_storage "$addr" 3 11 "full deliver holds pending[0]"

# eth_call observes the take's return value without mutating; the real take then advances the
# head, keeps the popped slot stale, and the next delivery wraps back to physical slot 0.
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'take()(uint64)')" 11 \
  "take returns the front message"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'take()' >/dev/null
solana_lean_require_storage "$addr" 7 1 "take advances head"
solana_lean_require_storage "$addr" 8 3 "take shrinks live"
solana_lean_require_storage "$addr" 3 11 "taken slot stays stale and unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 22 \
  "front view after take"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 55 >/dev/null
solana_lean_require_storage "$addr" 3 55 "wrapped delivery reuses pending[0]"
solana_lean_require_storage "$addr" 8 4 "wrapped delivery refills live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 22 \
  "front view across the wrap boundary"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 2)" 44 "wrapped live read 2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 3)" 55 "wrapped live read 3"

# Draining returns the FIFO order across the wrap and canonicalizes the head back to 0 on empty.
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'take()(uint64)')" 22 \
  "take 1 returns the wrapped front"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'take()' >/dev/null
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'take()(uint64)')" 33 \
  "take 2"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'take()' >/dev/null
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'take()(uint64)')" 44 \
  "take 3"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'take()' >/dev/null
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'take()(uint64)')" 55 \
  "take 4 returns the wrapped newest element"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'take()' >/dev/null
solana_lean_require_storage "$addr" 7 0 "emptied take canonicalizes head"
solana_lean_require_storage "$addr" 8 0 "emptied take clears live"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 0 \
  "front view on emptied mailbox"

# Empty take reverts with the typed empty() error and stores nothing.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'take()')" 'empty()' "empty take"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'take()' >/dev/null 2>&1; then
  echo "FAIL: empty take unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 8 0 "empty take holds live"

# purge resets only the canonical metadata; stale backing slots stay unreachable until reused.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 66 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'purge()' >/dev/null
solana_lean_require_storage "$addr" 7 0 "purge clears head"
solana_lean_require_storage "$addr" 8 0 "purge clears live"
solana_lean_require_storage "$addr" 3 66 "purge leaves stale pending[0] unreachable"
solana_lean_require_storage "$addr" 4 22 "purge leaves stale pending[1] unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 0 \
  "front view after purge"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'messageAt(uint64)(uint64)' 0)" 0 "purged read is the 0 fallback despite stale slots"

# Deliveries after a purge reuse the stale backing slots from the canonical empty state.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'deliver(uint64)' 77 >/dev/null
solana_lean_require_storage "$addr" 3 77 "post-purge delivery overwrites pending[0]"
solana_lean_require_storage "$addr" 4 22 "post-purge delivery leaves stale pending[1] unreachable"
solana_lean_require_storage "$addr" 8 1 "post-purge live"

# Inject impossible metadata and prove no mutation silently repairs malformed persistent state.
solana_lean_set_storage_word "$addr" 7 5
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 0 \
  "malformed head closes the front view"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'deliver(uint64)' 88)" 'malformed()' "malformed deliver"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'take()')" 'malformed()' "malformed take"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'purge()')" 'malformed()' "malformed purge"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'purge()' >/dev/null 2>&1; then
  echo "FAIL: malformed purge unexpectedly repaired head" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 5 "malformed mutations hold head"
solana_lean_require_storage "$addr" 8 1 "malformed mutations hold live"

solana_lean_set_storage_word "$addr" 8 6
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'deliver(uint64)' 88)" 'malformed()' "malformed live deliver"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'take()')" 'malformed()' "malformed live take"
solana_lean_require_storage "$addr" 8 6 "malformed live mutations hold live"

# A masked non-canonical empty state (live 0 with head != 0) fails closed as well.
solana_lean_set_storage_word "$addr" 8 0
solana_lean_set_storage_word "$addr" 7 2
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'frontOf()(uint64)')" 0 \
  "masked empty head closes the front view"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'take()')" 'malformed()' "masked empty take"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'purge()')" 'malformed()' "masked empty purge"
solana_lean_require_storage "$addr" 7 2 "masked empty mutations hold head"

echo "evm-anvil-ring-mailbox: ok (reject-at-full ring mailbox deliver/take/purge + wraparound + full/empty/unauthorized/malformed + stale slots; engineering only)"
