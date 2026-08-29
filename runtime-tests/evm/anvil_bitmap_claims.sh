#!/usr/bin/env bash
# EvmClaimBitmap: permissionless one-time claims over the StorageBitmap persistent bitmap policy
# (capacity 130 bits = 3 words, so word 2 is a partial word holding exactly bits 128 and 129).
# Covers claim success, claim replay (already()), the 63/64 word boundary, the final in-range
# bit 129, OOB rejection including the bit-130 aliasing probe, and persistent state across
# failed transactions.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-bitmap-claims
bin="$root/build/evm/EvmClaimBitmap.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18582}" "$root/build/evm/anvil-bitmap-claims.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

for slot in 0 1 2; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero claimed word $slot"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 0)" 0 "unclaimed bit 0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 129)" 0 "unclaimed final bit"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 130)" 0 "OOB read is the 0 fallback (no alias of bit 2)"

claimer_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"

# Permissionless claims at the word boundary from a second account.
"$cast" send --rpc-url "$rpc" --private-key "$claimer_key" "$addr" 'claim(uint64)' 63 >/dev/null
solana_lean_require_storage "$addr" 0 9223372036854775808 "claim sets bit 63 (word-0 top bit)"
"$cast" send --rpc-url "$rpc" --private-key "$claimer_key" "$addr" 'claim(uint64)' 64 >/dev/null
solana_lean_require_storage "$addr" 1 1 "claim sets bit 64 as word-1 mask 1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 63)" 1 "boundary read 63"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 64)" 1 "boundary read 64"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 62)" 0 "neighbor below the boundary stays clear"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 65)" 0 "neighbor above the boundary stays clear"

# Final in-range bit lives in the partial word 2.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'claim(uint64)' 129 >/dev/null
solana_lean_require_storage "$addr" 2 2 "claim sets final bit 129 in partial word 2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 129)" 1 "final-bit read"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 128)" 0 "bit 128 of the partial word stays clear"

# Claim replay reverts already() and stores nothing.
solana_lean_require_named_revert "$addr" "$("$cast" wallet address --private-key "$claimer_key")" \
  "$("$cast" calldata 'claim(uint64)' 63)" 'already()' "claim replay"
if "$cast" send --rpc-url "$rpc" --private-key "$claimer_key" \
    "$addr" 'claim(uint64)' 63 >/dev/null 2>&1; then
  echo "FAIL: claim replay unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 9223372036854775808 "replayed claim holds word 0"

# OOB claims revert oob() and store nothing; bit 130 (% 64 = 2, / 64 = 2) would alias bit 2 of
# the live partial word 2 without the fail-closed bounds gate.
solana_lean_require_named_revert "$addr" "$("$cast" wallet address --private-key "$private_key")" \
  "$("$cast" calldata 'claim(uint64)' 130)" 'oob()' "OOB claim at the capacity boundary"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'claim(uint64)' 130 >/dev/null 2>&1; then
  echo "FAIL: OOB claim unexpectedly succeeded (bit 130 aliased a lower bit)" >&2
  exit 1
fi
solana_lean_require_named_revert "$addr" "$("$cast" wallet address --private-key "$private_key")" \
  "$("$cast" calldata 'claim(uint64)' 18446744073709551615)" 'oob()' "huge OOB claim"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'claim(uint64)' 18446744073709551615 >/dev/null 2>&1; then
  echo "FAIL: huge OOB claim unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 2 2 "OOB claims hold partial word 2 (no aliasing)"
solana_lean_require_storage "$addr" 0 9223372036854775808 "OOB claims hold word 0"
solana_lean_require_storage "$addr" 1 1 "OOB claims hold word 1"

# New claims still succeed after every failed transaction above.
"$cast" send --rpc-url "$rpc" --private-key "$claimer_key" "$addr" 'claim(uint64)' 2 >/dev/null
solana_lean_require_storage "$addr" 0 9223372036854775812 "post-revert claim sets bit 2 in word 0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 2)" 1 "post-revert claim read"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 63)" 1 "bit 63 persists after reverts"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'hasClaimed(uint64)(uint64)' 129)" 1 "final bit persists after reverts"

echo "evm-anvil-bitmap-claims: ok (permissionless one-time claim + replay already() + 63/64 boundary + final bit 129 + OOB/no-alias + persistence; engineering only)"
