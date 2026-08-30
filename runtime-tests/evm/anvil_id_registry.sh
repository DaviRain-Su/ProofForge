#!/usr/bin/env bash
# EvmIdRegistry: permissionless capacity-3 enumerable UInt64 set at hashed namespace base 1.
# Covers key 0, duplicate/full/absent outcomes, middle/last/only swap-remove, enumeration after
# repair, non-reverting malformed membership fallback, and fail-closed mutation atomicity.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-id-registry
bin="$root/build/evm/EvmIdRegistry.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmIdRegistry.bin" >&2
  lake build Examples.EvmIdRegistry >/dev/null \
    || { echo "FAIL: lake build Examples.EvmIdRegistry failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmIdRegistry >/dev/null \
    || { echo "FAIL: build registered EvmIdRegistry failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18585}" "$root/build/evm/anvil-id-registry.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmIdRegistry.bin" >&2; exit 1; }
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

map_payload_slot() {
  local key="$1" base="$2" raw
  raw="$("$cast" index uint256 "$key" "$base")"
  "$python" -I -S -c "print(int('$raw', 16) + 1)"
}

for slot in 0 1 2 3; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero registry state"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sizeOf()(uint64)')" 0 \
  "empty size"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "key zero starts absent"

# Fill [10,0,30]. Key zero behaves like an ordinary member; duplicate and full failures are
# typed and preserve every static slot.
for id in 10 0 30; do
  solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
    'enroll(uint64)(bool)' "$id")" true "enroll $id returns true"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'enroll(uint64)' "$id" >/dev/null
done
solana_lean_require_storage "$addr" 0 10 "ids[0]"
solana_lean_require_storage "$addr" 1 0 "key zero occupies ids[1]"
solana_lean_require_storage "$addr" 2 30 "ids[2]"
solana_lean_require_storage "$addr" 3 3 "full count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 1 "key zero membership"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enroll(uint64)' 10)" 'duplicate()' "duplicate enroll"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enroll(uint64)' 40)" 'full()' "full registry enroll"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'enroll(uint64)' 40 >/dev/null 2>&1; then
  echo "FAIL: full registry enroll unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 3 "duplicate/full failures hold count"
solana_lean_require_storage "$addr" 2 30 "duplicate/full failures hold last id"

# Middle removal of key zero moves 30 into slot 1 and repairs its map position.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'release(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 1 30 "middle release moves final id"
solana_lean_require_storage "$addr" 3 2 "middle release decrements count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "released key zero is absent"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 30)" 1 "moved id map was repaired"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'idAt(uint64)(uint64)' 1)" 30 "enumeration observes moved id"

# Last removal keeps its stale backing slot unreachable; absent release returns false without a
# write. Removing the only remaining id reaches canonical empty state, then key zero can re-enter.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'release(uint64)' 30 >/dev/null
solana_lean_require_storage "$addr" 1 30 "last release keeps stale backing slot"
solana_lean_require_storage "$addr" 3 1 "last release decrements count"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'release(uint64)(bool)' 999)" false "absent release returns false"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'release(uint64)' 999 >/dev/null
solana_lean_require_storage "$addr" 3 1 "absent release holds count"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'release(uint64)' 10 >/dev/null
solana_lean_require_storage "$addr" 3 0 "only release reaches empty"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'enroll(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 0 0 "key zero reuses ids[0]"
solana_lean_require_storage "$addr" 3 1 "key zero re-enroll count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 1 "re-enrolled key zero membership"

# Forge key zero's map position beyond count. The non-reverting view returns 0, while enroll and
# release both fail malformed and preserve the forged evidence.
payload_slot="$(map_payload_slot 0 1)"
solana_lean_set_storage_word "$addr" "$payload_slot" 3
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "forged position uses non-reverting fallback"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enroll(uint64)' 0)" 'malformed()' "forged-position enroll"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'release(uint64)' 0)" 'malformed()' "forged-position release"
solana_lean_require_storage "$addr" 0 0 "forged-position failures hold backing"
solana_lean_require_storage "$addr" 3 1 "forged-position failures hold count"
solana_lean_require_storage "$addr" "$payload_slot" 3 "forged position is not repaired"

# A backing mismatch has the same view fallback and fail-closed mutation behavior.
solana_lean_set_storage_word "$addr" "$payload_slot" 1
solana_lean_set_storage_word "$addr" 0 8
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "backing mismatch uses non-reverting fallback"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'release(uint64)' 0)" 'malformed()' "backing mismatch release"
solana_lean_require_storage "$addr" 0 8 "backing mismatch is not repaired"
solana_lean_require_storage "$addr" 3 1 "backing mismatch holds count"

# Over-capacity count closes views and every mutation without silently repairing storage.
solana_lean_set_storage_word "$addr" 3 4
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "malformed count closes membership"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'idAt(uint64)(uint64)' 0)" 0 "malformed count closes enumeration"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'enroll(uint64)' 9)" 'malformed()' "malformed-count enroll"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'release(uint64)' 0)" 'malformed()' "malformed-count release"
solana_lean_require_storage "$addr" 3 4 "malformed mutations do not repair count"

echo "evm-anvil-id-registry: ok (key0 + duplicate/full/absent + middle/last/only remove + enumeration repair + malformed fallback/mutation atomicity; engineering only)"
