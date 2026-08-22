#!/usr/bin/env bash
# Flag: UInt8 in slot 0, UInt64 count in slot 1. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-flag
bin="$root/build/evm/Flag.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18549}" "$root/build/evm/anvil-flag.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" \
  0 "ctor getFlag"
solana_lean_require_storage "$addr" 0 0 "ctor flag slot"
solana_lean_require_storage "$addr" 1 7 "ctor count slot"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setFlag(uint64)' 1 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" \
  1 "setFlag view"
solana_lean_require_storage "$addr" 0 1 "setFlag flag"
solana_lean_require_storage "$addr" 1 7 "setFlag keeps count"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setFlag(uint64)' 256 >/dev/null 2>&1; then
  echo "FAIL: setFlag(256) should revert" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 1 "overflow holds flag"
solana_lean_require_storage "$addr" 1 7 "overflow holds count"

echo "evm-anvil-flag: ok (u8 mask + count hold; engineering only)"
