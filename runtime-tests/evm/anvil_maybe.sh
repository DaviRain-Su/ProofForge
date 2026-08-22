#!/usr/bin/env bash
# Maybe: Option UInt64 as tag+payload. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-maybe
bin="$root/build/evm/Maybe.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${SOLANA_LEAN_EVM_PORT:-18550}" "$root/build/evm/anvil-maybe.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

require_leaves() {
  local a="$1" tag="$2" payload="$3" label="$4"
  solana_lean_require_storage "$a" 0 "$tag" "$label tag"
  solana_lean_require_storage "$a" 1 "$payload" "$label payload"
}

require_leaves "$addr" 0 0 "ctor"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'isSome()(uint64)')" \
  0 "ctor isSome"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getValue()(uint64)')" \
  0 "ctor getValue"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setSome(uint64)' 77 >/dev/null
require_leaves "$addr" 1 77 "setSome"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'isSome()(uint64)')" \
  1 "setSome isSome"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getValue()(uint64)')" \
  77 "setSome getValue"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setNone()' >/dev/null
require_leaves "$addr" 0 0 "setNone"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'isSome()(uint64)')" \
  0 "setNone isSome"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getValue()(uint64)')" \
  0 "setNone getValue"

echo "evm-anvil-maybe: ok (none/some/getValue; engineering only)"
