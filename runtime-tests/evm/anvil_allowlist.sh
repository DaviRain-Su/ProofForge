#!/usr/bin/env bash
# EvmAllowlist: owner-gated capacity-4 enumerable UInt64 set. Covers key 0, duplicate/full/
# absent/unauthorized outcomes, middle/last/only swap-remove, positional enumeration, malformed
# count/position/backing evidence, and atomic state preservation across failed transactions.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-allowlist
bin="$root/build/evm/EvmAllowlist.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmAllowlist.bin" >&2
  lake build Examples.EvmAllowlist >/dev/null \
    || { echo "FAIL: lake build Examples.EvmAllowlist failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmAllowlist >/dev/null \
    || { echo "FAIL: build registered EvmAllowlist failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18584}" "$root/build/evm/anvil-allowlist.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmAllowlist.bin" >&2; exit 1; }
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
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero enumerable state"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'adminOf()(address)')" \
  "$sender" "admin getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sizeOf()(uint64)')" 0 \
  "empty size"

# Owner authorization precedes collection policy and stores nothing.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'grant(uint64)' 7)" "$other" "non-owner grant"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'grant(uint64)' 7 >/dev/null 2>&1; then
  echo "FAIL: non-owner grant unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 0 "unauthorized grant holds count"

# Key 0 is ordinary data. Fill [0,11,22,33], pin enumeration and membership, then reject a
# duplicate and a fifth key atomically.
for key in 0 11 22 33; do
  solana_lean_require_equal "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
    'grant(uint64)(bool)' "$key")" true "grant $key returns true"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grant(uint64)' "$key" >/dev/null
done
solana_lean_require_storage "$addr" 3 0 "key zero occupies members[0]"
solana_lean_require_storage "$addr" 4 11 "members[1]"
solana_lean_require_storage "$addr" 5 22 "members[2]"
solana_lean_require_storage "$addr" 6 33 "members[3]"
solana_lean_require_storage "$addr" 7 4 "full count"
for pair in '0 0' '1 11' '2 22' '3 33'; do
  index="${pair%% *}"
  value="${pair#* }"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'memberAt(uint64)(uint64)' "$index")" "$value" "enumeration index $index"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'containsOf(uint64)(uint64)' "$value")" 1 "membership $value"
done
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'grant(uint64)' 11)" 'duplicate()' "duplicate grant"
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'grant(uint64)' 44)" "full grant"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grant(uint64)' 44 >/dev/null 2>&1; then
  echo "FAIL: full allowlist grant unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 4 "duplicate/full failures hold count"
solana_lean_require_storage "$addr" 6 33 "duplicate/full failures hold last value"

# Middle removal of 11 moves final key 33 into index 1 and repairs membership.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'revoke(uint64)' 11 >/dev/null
solana_lean_require_storage "$addr" 4 33 "middle remove moves final key"
solana_lean_require_storage "$addr" 7 3 "middle remove decrements count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 11)" 0 "removed middle key is absent"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 33)" 1 "moved key map was repaired"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'memberAt(uint64)(uint64)' 1)" 33 "enumeration observes moved key"

# Last removal of 22 and then only removal avoid a backing move (the stale physical value is
# deliberately retained but unreachable). Absent removal is the explicit false/no-write result.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'revoke(uint64)' 22 >/dev/null
solana_lean_require_storage "$addr" 5 22 "last removal keeps stale backing slot"
solana_lean_require_storage "$addr" 7 2 "last removal decrements count"
solana_lean_require_equal "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'revoke(uint64)(bool)' 999)" false "absent revoke returns false"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'revoke(uint64)' 999 >/dev/null
solana_lean_require_storage "$addr" 7 2 "absent revoke holds count"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'revoke(uint64)' 33 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'revoke(uint64)' 0 >/dev/null
solana_lean_require_storage "$addr" 7 0 "only removal reaches empty"
solana_lean_require_storage "$addr" 3 0 "only key zero remains stale as data"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'containsOf(uint64)(uint64)' 0)" 0 "removed key zero is absent"

# Forge a live key's map position beyond count. Both the strict membership view and every
# mutation fail malformed without repairing state.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'grant(uint64)' 7 >/dev/null
payload_slot="$(map_payload_slot 7 0)"
solana_lean_set_storage_word "$addr" "$payload_slot" 3
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'containsOf(uint64)' 7)" 'malformed()' "forged-position contains"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'revoke(uint64)' 7)" 'malformed()' "forged-position revoke"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'grant(uint64)' 7)" 'malformed()' "forged-position grant"
solana_lean_require_storage "$addr" 3 7 "forged-position failures hold backing"
solana_lean_require_storage "$addr" 7 1 "forged-position failures hold count"
solana_lean_require_storage "$addr" "$payload_slot" 3 "forged position is not repaired"

# Restore the position, corrupt the backing leaf, and then corrupt count. Every strict operation
# closes before a write, preserving the impossible evidence for diagnosis.
solana_lean_set_storage_word "$addr" "$payload_slot" 1
solana_lean_set_storage_word "$addr" 3 8
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'containsOf(uint64)' 7)" 'malformed()' "backing mismatch contains"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'revoke(uint64)' 7)" 'malformed()' "backing mismatch revoke"
solana_lean_require_storage "$addr" 3 8 "backing mismatch is not repaired"
solana_lean_require_storage "$addr" 7 1 "backing mismatch holds count"

solana_lean_set_storage_word "$addr" 7 5
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'memberAt(uint64)(uint64)' 0)" 0 "malformed count closes enumeration"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'grant(uint64)' 9)" 'malformed()' "malformed-count grant"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'revoke(uint64)' 7)" 'malformed()' "malformed-count revoke"
solana_lean_require_storage "$addr" 7 5 "malformed mutations do not repair count"

echo "evm-anvil-allowlist: ok (key0 + duplicate/full/absent/unauthorized + middle/last/only remove + forged position/backing/count fail-closed; engineering only)"
