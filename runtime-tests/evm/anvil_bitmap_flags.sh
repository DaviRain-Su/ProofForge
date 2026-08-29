#!/usr/bin/env bash
# EvmFeatureFlags: owner-managed feature flags over the StorageBitmap persistent bitmap policy
# (capacity 128 bits = 2 words). Covers enable/disable/toggle idempotence, the 63/64 word
# boundary, the final in-range bit 127, OOB rejection (no lower-bit aliasing), Unauthorized
# gates, and persistent state across failed transactions.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-bitmap-flags
bin="$root/build/evm/EvmFeatureFlags.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18581}" "$root/build/evm/anvil-bitmap-flags.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

owner_words="$("$python" -I -S -c "
b=bytes.fromhex('${sender#0x}')
print(int.from_bytes(b[0:8], 'little'), int.from_bytes(b[8:16], 'little'),
      int.from_bytes(b[16:20], 'little'))
")"
owner_w0="${owner_words%% *}"
rest="${owner_words#* }"
owner_w1="${rest%% *}"
owner_w2="${rest#* }"
solana_lean_require_storage "$addr" 0 "$owner_w0" "constructor owner.w0"
solana_lean_require_storage "$addr" 1 "$owner_w1" "constructor owner.w1"
solana_lean_require_storage "$addr" 2 "$owner_w2" "constructor owner.w2"
solana_lean_require_storage "$addr" 3 0 "constructor zero flags word 0"
solana_lean_require_storage "$addr" 4 0 "constructor zero flags word 1"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)')" \
  "$sender" "owner getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 0)" 0 "unset bit 0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 127)" 0 "unset final bit"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 128)" 0 "OOB read is the 0 fallback"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 18446744073709551615)" 0 "huge OOB read is the 0 fallback"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"

# Non-owner enable reverts Unauthorized(other) and stores nothing.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'enable(uint64)' 7)" "$other" "non-owner enable"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'enable(uint64)' 7 >/dev/null 2>&1; then
  echo "FAIL: non-owner enable unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 0 "unauthorized enable holds word 0"

# Enable bit 0 and the word-boundary bit 63 in word 0; enable is idempotent.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enable(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 3 1 "enable writes flags[0] bit 0"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enable(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 3 1 "enable of a set bit is an idempotent same-word write"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enable(uint64)' 63 >/dev/null
solana_lean_require_storage "$addr" 3 9223372036854775809 "enable sets the word-0 top bit"
solana_lean_require_storage "$addr" 4 0 "word-0 writes never touch word 1"

# Word boundary: bit 64 lands in word 1 as mask 1; final in-range bit 127 is word 1's top bit.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enable(uint64)' 64 >/dev/null
solana_lean_require_storage "$addr" 4 1 "enable writes flags[1] bit 64 as mask 1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 64)" 1 "boundary read"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enable(uint64)' 127 >/dev/null
solana_lean_require_storage "$addr" 4 9223372036854775809 "enable sets the final in-range bit 127"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 127)" 1 "final-bit read"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 126)" 0 "neighbor of the final bit stays clear"

# OOB mutations revert oob() and store nothing; index 128 does not alias bit 0 of word 0.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enable(uint64)' 128)" 'oob()' "OOB enable at the capacity boundary"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'enable(uint64)' 128 >/dev/null 2>&1; then
  echo "FAIL: OOB enable unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enable(uint64)' 18446744073709551615)" 'oob()' "huge OOB enable"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'enable(uint64)' 18446744073709551615 >/dev/null 2>&1; then
  echo "FAIL: huge OOB enable unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 9223372036854775809 "OOB enable holds word 0 (no aliasing)"
solana_lean_require_storage "$addr" 4 9223372036854775809 "OOB enable holds word 1"

# Toggle flips one bit and reports the new value; toggling twice restores the exact word.
word1_base="$("$python" -I -S -c 'print(2**63 + 1)')"
word1_toggled="$("$python" -I -S -c 'print(2**63 + 1 + 2**36)')"
solana_lean_require_uint "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'toggle(uint64)(uint64)' 100)" 1 "toggle sets and reports 1"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'toggle(uint64)' 100 >/dev/null
solana_lean_require_storage "$addr" 4 "$word1_toggled" "toggle sets bit 100 in word 1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 100)" 1 "toggled read"
solana_lean_require_uint "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'toggle(uint64)(uint64)' 100)" 0 "second toggle clears and reports 0"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'toggle(uint64)' 100 >/dev/null
solana_lean_require_storage "$addr" 4 "$word1_base" "second toggle restores the exact word"

# Disable clears exactly one bit, keeps neighbors, and is idempotent.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'disable(uint64)' 63 >/dev/null
solana_lean_require_storage "$addr" 3 1 "disable clears bit 63 and keeps bit 0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 63)" 0 "disabled read"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 0)" 1 "disable keeps the neighbor bit"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'disable(uint64)' 63 >/dev/null
solana_lean_require_storage "$addr" 3 1 "disable of a clear bit is an idempotent same-word write"

# Non-owner disable/toggle revert Unauthorized(other) and store nothing.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'disable(uint64)' 0)" "$other" "non-owner disable"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'disable(uint64)' 0 >/dev/null 2>&1; then
  echo "FAIL: non-owner disable unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'toggle(uint64)' 0)" "$other" "non-owner toggle"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'toggle(uint64)' 0 >/dev/null 2>&1; then
  echo "FAIL: non-owner toggle unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_named_revert "$addr" "$other" \
  "$("$cast" calldata 'toggle(uint64)' 500)" 'Unauthorized(address)' \
  "non-owner OOB toggle hits the owner gate first"
solana_lean_require_storage "$addr" 3 1 "unauthorized mutations hold word 0"
solana_lean_require_storage "$addr" 4 9223372036854775809 "unauthorized mutations hold word 1"

# Persistent state survives every failed transaction above.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 0)" 1 "bit 0 persists after reverts"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 64)" 1 "bit 64 persists after reverts"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isEnabled(uint64)(uint64)' 127)" 1 "bit 127 persists after reverts"

echo "evm-anvil-bitmap-flags: ok (owner-gated enable/disable/toggle + idempotence + 63/64 boundary + final bit + OOB/no-alias + unauthorized + persistence; engineering only)"
