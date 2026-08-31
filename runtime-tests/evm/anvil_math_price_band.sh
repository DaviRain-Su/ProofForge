#!/usr/bin/env bash
# Shared UInt64 math EVM consumer: bounded helpers, saturation, and integer logarithms.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-math-price-band
bin="$root/build/evm/EvmPriceBand.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18700}" "$root/build/evm/anvil-math-price-band.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"
max=18446744073709551615
half=9223372036854775807
half_up=9223372036854775808
sender="$("$cast" wallet address --private-key "$private_key")"

solana_lean_require_storage "$addr" 0 7 "constructor quote"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'lower(uint64,uint64)(uint64)' "$max" 7)" 7 "minimum boundary"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'upper(uint64,uint64)(uint64)' "$max" 7)" "$max" "maximum boundary"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'midpoint(uint64,uint64)(uint64)' 0 "$max")" "$half" "overflow-safe midpoint"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'binaryBand(uint64)(uint64)' 0)" 0 "binary log zero policy"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'binaryBand(uint64)(uint64)' 2)" 1 "binary log exact power"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'binaryBand(uint64)(uint64)' "$max")" 63 "binary log maximum"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'decimalBand(uint64)(uint64)' 9)" 0 "decimal log below first power"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'decimalBand(uint64)(uint64)' 10000000000000000000)" 19 "decimal log 10^19"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'byteBand(uint64)(uint64)' 255)" 0 "byte log below first power"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'byteBand(uint64)(uint64)' 256)" 1 "byte log exact power"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'byteBand(uint64)(uint64)' "$max")" 7 "byte log maximum"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'roundUp(uint64,uint64)(uint64)' "$max" 2)" "$half_up" "maximum ceil-div by two"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'roundUp(uint64,uint64)' "$max" 2 >/dev/null
solana_lean_require_storage "$addr" 0 "$half_up" "ceil-div persists"

solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'roundUp(uint64,uint64)' "$max" 0)" 'zeroTick()' \
  "zero denominator"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'roundUp(uint64,uint64)' "$max" 0 >/dev/null 2>&1; then
  echo "FAIL: zero denominator unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 "$half_up" "zero denominator is atomic"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'roundUp(uint64,uint64)' "$max" 1 >/dev/null
solana_lean_require_storage "$addr" 0 "$max" "ceil-div maximum by one"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'increase(uint64)(uint64)' 1)" "$max" "saturating increase at maximum"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'discount(uint64)' "$max" >/dev/null
solana_lean_require_storage "$addr" 0 0 "saturating discount floors at zero"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'scale(uint64)(uint64)' "$max")" 0 "zero scale avoids division"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'increase(uint64)' "$half_up" >/dev/null
solana_lean_require_storage "$addr" 0 "$half_up" "exact increase after zero"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'scale(uint64)(uint64)' 2)" "$max" "saturating scale preview"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'scale(uint64)' 2 >/dev/null
solana_lean_require_storage "$addr" 0 "$max" "saturating scale persists"

echo "evm-anvil-math-price-band: ok (bounded/saturating/logarithmic UInt64 math; engineering only)"
