#!/usr/bin/env bash
# EvmStaticRoster: static Address/fixed-record-vector/bool layout and bounded writes.
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

echo "evm-anvil-static-roster: ok (address/fixed-vector/bool slots + bounds; engineering only)"
