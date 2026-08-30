#!/usr/bin/env bash
# EvmConfigMap: owner-gated capacity-4 enumerable UInt64-to-UInt64 map. Covers key/value zero,
# insert/update/full/absent/unauthorized behavior, middle/last/only swap-remove with both hashed
# namespaces, forged position/backing/count evidence, and failed-transaction atomicity.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-config-map
bin="$root/build/evm/EvmConfigMap.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmConfigMap.bin" >&2
  lake build Examples.EvmConfigMap >/dev/null \
    || { echo "FAIL: lake build Examples.EvmConfigMap failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmConfigMap >/dev/null \
    || { echo "FAIL: build registered EvmConfigMap failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18588}" "$root/build/evm/anvil-config-map.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmConfigMap.bin" >&2; exit 1; }
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"

map_payload_slot() {
  local key="$1" base="$2" raw
  raw="$("$cast" index uint256 "$key" "$base")"
  "$python" -I -S -c "print(int('$raw', 16) + 1)"
}

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
for slot in 3 4 5 6 7; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero table state"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sizeOf()(uint64)')" 0 \
  "empty size"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'valueOf(uint64)(uint64)' 0)" 0 "key zero starts absent"

# Authorization precedes map policy and preserves both static and hashed state.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'write(uint64,uint64)' 7 70)" "$other" "non-owner write"
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'remove(uint64)' 7)" "$other" "non-owner remove"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'write(uint64,uint64)' 7 70 >/dev/null 2>&1; then
  echo "FAIL: non-owner write unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 0 "unauthorized write holds count"

# Fill [0→0, 11→110, 22→220, 33→330]. Key zero and value zero are ordinary data. Updating an
# existing key remains legal when full, while growing to a fifth key fails atomically.
for pair in '0 0' '11 110' '22 220' '33 330'; do
  key="${pair%% *}"
  value="${pair#* }"
  solana_lean_require_equal "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
    'write(uint64,uint64)(bool)' "$key" "$value")" true "write $key returns true"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'write(uint64,uint64)' "$key" "$value" >/dev/null
done
solana_lean_require_storage "$addr" 3 0 "key zero occupies keys[0]"
solana_lean_require_storage "$addr" 4 11 "keys[1]"
solana_lean_require_storage "$addr" 5 22 "keys[2]"
solana_lean_require_storage "$addr" 6 33 "keys[3]"
solana_lean_require_storage "$addr" 7 4 "full count"
for triple in '0 0 0' '1 11 110' '2 22 220' '3 33 330'; do
  index="${triple%% *}"
  tail="${triple#* }"
  key="${tail%% *}"
  value="${tail#* }"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'keyAt(uint64)(uint64)' "$index")" "$key" "key enumeration index $index"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'valueAt(uint64)(uint64)' "$index")" "$value" "value enumeration index $index"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'valueOf(uint64)(uint64)' "$key")" "$value" "lookup key $key"
done
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'write(uint64,uint64)' 11 111 >/dev/null
solana_lean_require_storage "$addr" 7 4 "full update does not grow count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'valueOf(uint64)(uint64)' 11)" 111 "full update replaces value"
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'write(uint64,uint64)' 44 440)" "full map growth"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'write(uint64,uint64)' 44 440 >/dev/null 2>&1; then
  echo "FAIL: full config-map growth unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 4 "full growth failure holds count"
solana_lean_require_storage "$addr" "$(map_payload_slot 44 0)" 0 \
  "full growth writes no position"
solana_lean_require_storage "$addr" "$(map_payload_slot 44 1)" 0 \
  "full growth writes no value"

# Middle removal moves key 33 into index 1, repairs only its position, and clears both namespaces
# for key 11. The moved key's value remains keyed by identity.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'remove(uint64)' 11 >/dev/null
solana_lean_require_storage "$addr" 4 33 "middle remove moves final key"
solana_lean_require_storage "$addr" 7 3 "middle remove decrements count"
solana_lean_require_storage "$addr" "$(map_payload_slot 11 0)" 0 \
  "middle remove clears removed position"
solana_lean_require_storage "$addr" "$(map_payload_slot 11 1)" 0 \
  "middle remove clears removed value"
solana_lean_require_storage "$addr" "$(map_payload_slot 33 0)" 2 \
  "middle remove repairs moved position"
solana_lean_require_storage "$addr" "$(map_payload_slot 33 1)" 330 \
  "middle remove preserves moved value"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'valueAt(uint64)(uint64)' 1)" 330 "enumeration observes moved value"

# Last and only removals do not rewrite stale backing lanes, but clear both map namespaces.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'remove(uint64)' 22 >/dev/null
solana_lean_require_storage "$addr" 5 22 "last remove keeps stale backing key"
solana_lean_require_storage "$addr" 7 2 "last remove decrements count"
solana_lean_require_storage "$addr" "$(map_payload_slot 22 0)" 0 \
  "last remove clears position"
solana_lean_require_storage "$addr" "$(map_payload_slot 22 1)" 0 \
  "last remove clears value"
solana_lean_require_equal "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'remove(uint64)(bool)' 999)" false "absent remove returns false"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'remove(uint64)' 999 >/dev/null
solana_lean_require_storage "$addr" 7 2 "absent remove holds count"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'remove(uint64)' 33 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'remove(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 7 0 "only remove reaches empty"
solana_lean_require_storage "$addr" "$(map_payload_slot 0 0)" 0 \
  "key-zero removal clears position"
solana_lean_require_storage "$addr" "$(map_payload_slot 0 1)" 0 \
  "key-zero removal clears zero value"

# Forge one live key's position beyond count. Strict lookup and both mutations fail malformed,
# preserving its backing key, value, count, and forged evidence.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'write(uint64,uint64)' 7 70 >/dev/null
position_slot="$(map_payload_slot 7 0)"
value_slot="$(map_payload_slot 7 1)"
solana_lean_set_storage_word "$addr" "$position_slot" 3
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'valueOf(uint64)' 7)" 'malformed()' "forged-position lookup"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'write(uint64,uint64)' 7 71)" 'malformed()' "forged-position update"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'remove(uint64)' 7)" 'malformed()' "forged-position remove"
solana_lean_require_storage "$addr" 3 7 "forged failures hold backing"
solana_lean_require_storage "$addr" 7 1 "forged failures hold count"
solana_lean_require_storage "$addr" "$position_slot" 3 "forged position is not repaired"
solana_lean_require_storage "$addr" "$value_slot" 70 "forged failures hold value"

# Restore position, corrupt backing, then corrupt count. Every strict mutation remains fail-closed.
solana_lean_set_storage_word "$addr" "$position_slot" 1
solana_lean_set_storage_word "$addr" 3 8
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'valueOf(uint64)' 7)" 'malformed()' "backing mismatch lookup"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'remove(uint64)' 7)" 'malformed()' "backing mismatch remove"
solana_lean_require_storage "$addr" 3 8 "backing mismatch is not repaired"
solana_lean_require_storage "$addr" "$value_slot" 70 "backing mismatch holds value"

solana_lean_set_storage_word "$addr" 7 5
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'keyAt(uint64)(uint64)' 0)" 0 "malformed count closes key enumeration"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'valueAt(uint64)(uint64)' 0)" 0 "malformed count closes value enumeration"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'write(uint64,uint64)' 9 90)" 'malformed()' "malformed-count write"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'remove(uint64)' 7)" 'malformed()' "malformed-count remove"
solana_lean_require_storage "$addr" 7 5 "malformed mutations do not repair count"

echo "evm-anvil-config-map: ok (key/value zero + insert/update/full/absent/unauthorized + dual-map middle/last/only remove + malformed atomicity; engineering only)"
