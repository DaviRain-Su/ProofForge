#!/usr/bin/env bash
# Wide: UInt256 ABI + checked add/sub/mul. Darwin + Linux.
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

echo "evm-anvil-wide: ok (uint256 add/sub/mul; engineering only)"
