#!/usr/bin/env bash
# Window: fixed Vector leaves and dynamic update. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-window
bin="$root/build/evm/Window.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18557}" "$root/build/evm/anvil-window.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getHead()(uint64)')" \
  7 "constructor getHead"
solana_lean_require_storage "$addr" 0 7 "constructor head"
solana_lean_require_storage "$addr" 1 0 "constructor tail"

simulated="$("$cast" call --rpc-url "$rpc" "$addr" 'setTail(uint64)(uint64)' 9)"
solana_lean_require_uint "$simulated" 9 "setTail return"
solana_lean_require_storage "$addr" 0 7 "eth_call keeps head"
solana_lean_require_storage "$addr" 1 0 "eth_call does not commit tail"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setTail(uint64)' 9 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getHead()(uint64)')" \
  7 "setTail keeps getHead"
solana_lean_require_storage "$addr" 0 7 "setTail keeps head"
solana_lean_require_storage "$addr" 1 9 "setTail writes tail"

echo "evm-anvil-window: ok (ctor/vector set/head hold; engineering only)"
