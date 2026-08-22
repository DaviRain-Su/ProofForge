#!/usr/bin/env bash
# Lang: bitwise, bounded for, runtime index, uint8 ABI, tuple return, named revert.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-lang
bin="$root/build/evm/Lang.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18553}" "$root/build/evm/anvil-lang.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 3)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  3 "ctor get"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'band(uint64,uint64)(uint64)' 0xf0 0x0f)" \
  0 "band"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'bor(uint64,uint64)(uint64)' 0xf0 0x0f)" \
  255 "bor"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'bxor(uint64,uint64)(uint64)' 255 15)" \
  240 "bxor"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'bnot(uint64)(uint64)' 0)" \
  18446744073709551615 "bnot"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shl(uint64,uint64)(uint64)' 1 3)" \
  8 "shl"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shr(uint64,uint64)(uint64)' 8 3)" \
  1 "shr"

if "$cast" call --rpc-url "$rpc" "$addr" 'shl(uint64,uint64)(uint64)' 1 64 >/dev/null 2>&1; then
  echo "FAIL: shl count 64 should revert" >&2
  exit 1
fi

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'mask8(uint8)(uint64)' 7)" \
  7 "mask8"

if "$cast" call --rpc-url "$rpc" "$addr" 'mask8(uint8)(uint64)' 256 >/dev/null 2>&1; then
  echo "FAIL: mask8(256) should revert" >&2
  exit 1
fi

pair="$("$cast" call --rpc-url "$rpc" "$addr" 'both()(uint64,uint64)')"
left="$(printf '%s\n' "$pair" | head -n1)"
right="$(printf '%s\n' "$pair" | tail -n1)"
solana_lean_require_uint "$left" 3 "both.left"
solana_lean_require_uint "$right" 0 "both.right"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setAt(uint64,uint64)' 1 9 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getAt(uint64)(uint64)' 1)" \
  9 "getAt after set"
solana_lean_require_storage "$addr" 0 3 "setAt keeps cells_0"
solana_lean_require_storage "$addr" 1 9 "setAt wrote cells_1"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setAt(uint64,uint64)' 4 1 >/dev/null 2>&1; then
  echo "FAIL: setAt(4) should revert oob" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 1 9 "oob holds cells_1"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sum4()(uint64)')" \
  12 "sum4 = 3+9+0+0"

echo "evm-anvil-lang: ok (bits/for/index/abi/tuple/oob; engineering only)"
