#!/usr/bin/env bash
# Wide: UInt256 ABI + checked arithmetic, comparisons, bitwise operations, and shifts. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-wide
bin="$root/build/evm/Wide.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18557}" "$root/build/evm/anvil-wide.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Wide.bin" >&2; exit 1; }

addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'echo(uint256)(uint256)' 7)" \
  7 "echo uint256"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'add(uint256,uint256)(uint256)' 1 2)" \
  3 "1+2"

wide="$("$python" -I -S -c "print((1<<64)+1)")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'add(uint256,uint256)(uint256)' "$wide" 2)" \
  "$("$python" -I -S -c "print((1<<64)+3)")" "2^64+1 plus 2"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'sub(uint256,uint256)(uint256)' "$wide" 1)" \
  "$("$python" -I -S -c "print(1<<64)")" "2^64+1 minus 1"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'mul(uint256,uint256)(uint256)' "$("$python" -I -S -c "print(1<<64)")" 2)" \
  "$("$python" -I -S -c "print(1<<65)")" "2^64 * 2"

cmp_a="$("$python" -I -S -c "print((1<<192)+(7<<64)+3)")"
cmp_b="$("$python" -I -S -c "print((1<<192)+(8<<64)+1)")"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'eq256(uint256,uint256)(bool)' "$cmp_a" "$cmp_a")" true "uint256 equality"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'eq256(uint256,uint256)(bool)' "$cmp_a" "$cmp_b")" false "uint256 inequality"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'lt256(uint256,uint256)(bool)' "$cmp_a" "$cmp_b")" true "uint256 less-than"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'le256(uint256,uint256)(bool)' "$cmp_b" "$cmp_b")" true "uint256 less-or-equal"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'gt256(uint256,uint256)(bool)' "$cmp_b" "$cmp_a")" true "uint256 greater-than"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ge256(uint256,uint256)(bool)' "$cmp_a" "$cmp_b")" false "uint256 greater-or-equal"

bit_a="$("$python" -I -S -c "print((1<<255)+(0xf0<<64)+0x55)")"
bit_b="$("$python" -I -S -c "print((1<<200)+(0x0f<<64)+0xaa)")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'bitAnd(uint256,uint256)(uint256)' "$bit_a" "$bit_b")" \
  "$("$python" -I -S -c "print($bit_a & $bit_b)")" "uint256 bitwise and"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'bitOr(uint256,uint256)(uint256)' "$bit_a" "$bit_b")" \
  "$("$python" -I -S -c "print($bit_a | $bit_b)")" "uint256 bitwise or"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'bitXor(uint256,uint256)(uint256)' "$bit_a" "$bit_b")" \
  "$("$python" -I -S -c "print($bit_a ^ $bit_b)")" "uint256 bitwise xor"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'complement(uint256)(uint256)' "$bit_a")" \
  "$("$python" -I -S -c "print(((1<<256)-1) ^ $bit_a)")" "uint256 complement"

shift_value="$("$python" -I -S -c "print((1<<192)+3)")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'shiftLeft(uint256,uint64)(uint256)' "$shift_value" 65)" \
  "$("$python" -I -S -c "print(($shift_value << 65) & ((1<<256)-1))")" "uint256 shift left"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'shiftRight(uint256,uint64)(uint256)' "$shift_value" 65)" \
  "$("$python" -I -S -c "print($shift_value >> 65)")" "uint256 shift right"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'shiftLeft(uint256,uint64)(uint256)' "$shift_value" 256)" 0 "uint256 wide shift is zero"

dividend="$("$python" -I -S -c "print((1<<200)+(17<<64)+12345)")"
divisor="$("$python" -I -S -c "print((1<<96)+7)")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'div256(uint256,uint256)(uint256)' "$dividend" "$divisor")" \
  "$("$python" -I -S -c "print($dividend // $divisor)")" "uint256 cross-limb division"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'mod256(uint256,uint256)(uint256)' "$dividend" "$divisor")" \
  "$("$python" -I -S -c "print($dividend % $divisor)")" "uint256 cross-limb modulo"
if "$cast" call --rpc-url "$rpc" "$addr" \
    'div256(uint256,uint256)(uint256)' "$dividend" 0 >/dev/null 2>&1; then
  echo "FAIL: division by zero unexpectedly succeeded" >&2
  exit 1
fi
if "$cast" call --rpc-url "$rpc" "$addr" \
    'mod256(uint256,uint256)(uint256)' "$dividend" 0 >/dev/null 2>&1; then
  echo "FAIL: modulo by zero unexpectedly succeeded" >&2
  exit 1
fi

u128="$("$python" -I -S -c "print((1<<127)+(1<<64)+7)")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'echo128(uint128)(uint128)' "$u128")" "$u128" "shared uint128 echo"

bytes12="0x00112233445566778899aabb"
got_bytes12="$("$cast" call --rpc-url "$rpc" "$addr" \
  'echoBytes12(bytes12)(bytes12)' "$bytes12")"
solana_lean_require_equal "${got_bytes12,,}" "$bytes12" "shared bytes12 echo"

u128_selector="$("$cast" sig 'echo128(uint128)')"
bad_u128="${u128_selector}0000000000000000000000000000000100000000000000000000000000000007"
if "$cast" call --rpc-url "$rpc" "$addr" --data "$bad_u128" >/dev/null 2>&1; then
  echo "FAIL: uint128 high-bit padding unexpectedly succeeded" >&2
  exit 1
fi

bytes12_selector="$("$cast" sig 'echoBytes12(bytes12)')"
bad_bytes12="${bytes12_selector}${bytes12#0x}0000000000000000000000000000000000000001"
if "$cast" call --rpc-url "$rpc" "$addr" --data "$bad_bytes12" >/dev/null 2>&1; then
  echo "FAIL: bytes12 right padding unexpectedly succeeded" >&2
  exit 1
fi

max="0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
if "$cast" call --rpc-url "$rpc" "$addr" \
    'add(uint256,uint256)(uint256)' "$max" 1 >/dev/null 2>&1; then
  echo "FAIL: add overflow unexpectedly succeeded" >&2
  exit 1
fi
if "$cast" call --rpc-url "$rpc" "$addr" \
    'sub(uint256,uint256)(uint256)' 0 1 >/dev/null 2>&1; then
  echo "FAIL: sub underflow unexpectedly succeeded" >&2
  exit 1
fi
if "$cast" call --rpc-url "$rpc" "$addr" \
    'mul(uint256,uint256)(uint256)' "$wide" "$max" >/dev/null 2>&1; then
  echo "FAIL: mul overflow unexpectedly succeeded" >&2
  exit 1
fi

echo "evm-anvil-wide: ok (uint256 arithmetic/ordering/bitwise/divmod + uint128/bytes12 ABI; engineering only)"
