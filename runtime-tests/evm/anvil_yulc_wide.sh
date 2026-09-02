#!/usr/bin/env bash
# Dual-backend Anvil gate: Wide uint256 ABI with solc vs yulc bytecode (E-B3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-wide
solana_lean_yulc_or_skip evm-anvil-yulc-wide

out="$root/build/evm-yulc-anvil-wide"
solana_lean_dual_build_program Wide "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-wide

solana_lean_start_anvil "${PF_EVM_PORT:-18595}" "$root/build/evm/anvil-yulc-wide.log"

run_wide_suite() {
  local label="$1" bytecode="$2"
  local addr wide cmp_a cmp_b
  addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'echo(uint256)(uint256)' 7)" \
    7 "$label: echo uint256"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'add(uint256,uint256)(uint256)' 1 2)" \
    3 "$label: 1+2"

  wide="$("$python" -I -S -c "print((1<<64)+1)")"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'add(uint256,uint256)(uint256)' "$wide" 2)" \
    "$("$python" -I -S -c "print((1<<64)+3)")" "$label: wide add"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sub(uint256,uint256)(uint256)' "$wide" 1)" \
    "$("$python" -I -S -c "print(1<<64)")" "$label: wide sub"

  cmp_a="$("$python" -I -S -c "print((1<<192)+(7<<64)+3)")"
  cmp_b="$("$python" -I -S -c "print((1<<192)+(8<<64)+1)")"
  solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'lt256(uint256,uint256)(bool)' "$cmp_a" "$cmp_b")" \
    true "$label: uint256 less-than"

  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'bitAnd(uint256,uint256)(uint256)' \
    "$("$python" -I -S -c "print((1<<255)+(0xf0<<64)+0x55)")" \
    "$("$python" -I -S -c "print((1<<200)+(0x0f<<64)+0xaa)")")" \
    "$("$python" -I -S -c "print(((1<<255)+(0xf0<<64)+0x55) & ((1<<200)+(0x0f<<64)+0xaa))")" \
    "$label: bitwise and"

  if "$cast" call --rpc-url "$rpc" "$addr" \
      'add(uint256,uint256)(uint256)' \
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 1 >/dev/null 2>&1; then
    echo "FAIL: $label add overflow unexpectedly succeeded" >&2
    exit 1
  fi
  echo "$addr"
}

solc_addr="$(run_wide_suite solc "$SOLC_HEX")"
yulc_addr="$(run_wide_suite yulc "$YULC_HEX")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'echo(uint256)(uint256)' 99)" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'echo(uint256)(uint256)' 99)" \
  "solc vs yulc echo mismatch"

echo "evm-anvil-yulc-wide: ok (dual-backend behavior match; engineering only)"
