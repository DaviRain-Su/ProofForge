#!/usr/bin/env bash
# EvmStaticRoster: static Address/fixed-record-vector/bool layout, bounded writes, and the
# bounded static writer role set (EVM-SDK-3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-static-roster
bin="$root/build/evm/EvmStaticRoster.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18564}" "$root/build/evm/anvil-static-roster.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
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
for slot in 3 4 5 6 7 8 9; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero seat/closed slot"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'adminOf()(address)')" \
  "$sender" "admin getter"

# seats[1] occupies slots 5/6; adjacent records and the closed flag must remain untouched.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setSeat(uint64,uint64,uint8)' 1 42 3 >/dev/null
solana_lean_require_storage "$addr" 5 42 "seat[1].points targeted mutation"
solana_lean_require_storage "$addr" 6 3 "seat[1].tier targeted mutation"
for slot in 3 4 7 8 9; do
  solana_lean_require_storage "$addr" "$slot" 0 "neighboring seat/closed slot holds"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'seatPoints(uint64)(uint64)' 1)" 42 "seat points getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'seatTier(uint64)(uint8)' 1)" 3 "seat tier getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'seatPoints(uint64)(uint64)' 3)" 0 "bounded getter OOB"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setSeat(uint64,uint64,uint8)' 3 99 7 >/dev/null 2>&1; then
  echo "FAIL: out-of-bounds seat update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 5 42 "OOB update holds selected seat"
solana_lean_require_storage "$addr" 7 0 "OOB update cannot spill into next slot"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setSeat(uint64,uint64,uint8)' 0 9 2)" "$other" \
  "non-admin seat update"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setSeat(uint64,uint64,uint8)' 0 9 2 >/dev/null 2>&1; then
  echo "FAIL: non-admin seat update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 0 "unauthorized update holds seat[0]"

# EVM-SDK-3 roles: bounded static writer set, two explicit address slots (10..15).
zero_addr="0x0000000000000000000000000000000000000000"
wr2="0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC"
wr3="0x90F79bf6EB2c4f870365E785982E1f101E93b906"

writer_limbs() {
  "$python" -I -S -c "
b=bytes.fromhex('${1#0x}')
print(int.from_bytes(b[0:8], 'little'), int.from_bytes(b[8:16], 'little'),
      int.from_bytes(b[16:20], 'little'))
"
}

for slot in 10 11 12 13 14 15; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor writer slot vacant"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isWriter(address)(bool)' "$other")" false "vacant membership view"

# Non-admin grant reverts Unauthorized(other) and cannot mutate the role slots.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'grantWriter(address)' "$other")" "$other" "non-admin writer grant"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'grantWriter(address)' "$other" >/dev/null 2>&1; then
  echo "FAIL: non-admin writer grant unexpectedly succeeded" >&2
  exit 1
fi
for slot in 10 11 12; do
  solana_lean_require_storage "$addr" "$slot" 0 "unauthorized grant holds writer slot0"
done

# Zero candidate reverts ZeroAddress().
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'grantWriter(address)' "$zero_addr")" "zero writer grant"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grantWriter(address)' "$zero_addr" >/dev/null 2>&1; then
  echo "FAIL: zero writer grant unexpectedly succeeded" >&2
  exit 1
fi

# Admin grant fills slot 0 only (slots 10..12 = address limbs; 13..15 stay zero).
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grantWriter(address)' "$other" >/dev/null
read -r ow0 ow1 ow2 <<< "$(writer_limbs "$other")"
solana_lean_require_storage "$addr" 10 "$ow0" "grant writer slot0 w0"
solana_lean_require_storage "$addr" 11 "$ow1" "grant writer slot0 w1"
solana_lean_require_storage "$addr" 12 "$ow2" "grant writer slot0 w2"
for slot in 13 14 15; do
  solana_lean_require_storage "$addr" "$slot" 0 "grant leaves writer slot1 vacant"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isWriter(address)(bool)' "$other")" true "membership view after grant"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isWriter(address)(bool)' "$sender")" false "nonmember view after grant"

# Duplicate grant is a successful idempotent no-op: nothing moves.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grantWriter(address)' "$other" >/dev/null
for slot in 13 14 15; do
  solana_lean_require_storage "$addr" "$slot" 0 "duplicate grant holds writer slot1 vacant"
done
solana_lean_require_storage "$addr" 10 "$ow0" "duplicate grant holds writer slot0"

# Second distinct grant fills slot 1 (slots 13..15).
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grantWriter(address)' "$wr2" >/dev/null
read -r pw0 pw1 pw2 <<< "$(writer_limbs "$wr2")"
solana_lean_require_storage "$addr" 13 "$pw0" "grant writer slot1 w0"
solana_lean_require_storage "$addr" 14 "$pw1" "grant writer slot1 w1"
solana_lean_require_storage "$addr" 15 "$pw2" "grant writer slot1 w2"

# Full set reverts CapExceeded().
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'grantWriter(address)' "$wr3")" "full writer set grant"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grantWriter(address)' "$wr3" >/dev/null 2>&1; then
  echo "FAIL: full-set writer grant unexpectedly succeeded" >&2
  exit 1
fi

# Nonmember revoke is a successful idempotent no-op.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'revokeWriter(address)' "$wr3" >/dev/null
solana_lean_require_storage "$addr" 10 "$ow0" "nonmember revoke holds writer slot0"
solana_lean_require_storage "$addr" 13 "$pw0" "nonmember revoke holds writer slot1"

# Non-admin revoke reverts Unauthorized(other) and cannot clear a slot.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'revokeWriter(address)' "$wr2")" "$other" "non-admin writer revoke"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'revokeWriter(address)' "$wr2" >/dev/null 2>&1; then
  echo "FAIL: non-admin writer revoke unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 13 "$pw0" "unauthorized revoke holds writer slot1"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'close()' >/dev/null
solana_lean_require_storage "$addr" 9 1 "closed flag targeted mutation"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'closedOf()(bool)')" \
  true "closed getter"
solana_lean_require_paused "$addr" "$sender" \
  "$("$cast" calldata 'setSeat(uint64,uint64,uint8)' 1 99 7)" "closed seat update"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setSeat(uint64,uint64,uint8)' 1 99 7 >/dev/null 2>&1; then
  echo "FAIL: closed roster update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 5 42 "closed update holds points"
solana_lean_require_storage "$addr" 6 3 "closed update holds tier"

# A closed roster rejects further grants with Paused() but still allows revocation, so
# membership can be wound down: revoking the slot-0 writer clears exactly slots 10..12.
solana_lean_require_paused "$addr" "$sender" \
  "$("$cast" calldata 'grantWriter(address)' "$wr3")" "closed writer grant"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grantWriter(address)' "$wr3" >/dev/null 2>&1; then
  echo "FAIL: closed roster writer grant unexpectedly succeeded" >&2
  exit 1
fi

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'revokeWriter(address)' "$other" >/dev/null
for slot in 10 11 12; do
  solana_lean_require_storage "$addr" "$slot" 0 "closed revoke clears writer slot0"
done
solana_lean_require_storage "$addr" 13 "$pw0" "closed revoke holds writer slot1"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isWriter(address)(bool)' "$other")" false "membership cleared after closed revoke"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'isWriter(address)(bool)' "$wr2")" true "other writer survives closed revoke"

echo "evm-anvil-static-roster: ok (address/fixed-vector/bool slots + bounds + bounded writer roles; engineering only)"
