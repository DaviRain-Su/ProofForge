#!/usr/bin/env bash
# Const: constructor immutables. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-const
bin="$root/build/evm/Const.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18556}" "$root/build/evm/anvil-const.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Const.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
peer="$("$cast" wallet address --private-key 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)"
encoded="$("$cast" abi-encode 'constructor(uint64,uint64,address,address)' 7 3 "$sender" "$peer")"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  --create "0x${bytecode}${encoded#0x}")"
addr="$(printf '%s' "$receipt" | solana_lean_contract_address)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'seedOf()(uint64)')" \
  7 "immutable seed"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'saltOf()(uint64)')" \
  3 "immutable salt"
got_who="$("$cast" call --rpc-url "$rpc" "$addr" 'whoOf()(address)')"
solana_lean_require_equal "${got_who,,}" "${sender,,}" "immutable who"
got_peer="$("$cast" call --rpc-url "$rpc" "$addr" 'peerOf()(address)')"
solana_lean_require_equal "${got_peer,,}" "${peer,,}" "immutable peer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  0 "dummy starts at 0"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'touch(uint64)' 11 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  11 "dummy after touch"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'seedOf()(uint64)')" \
  7 "immutable seed holds after touch"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'saltOf()(uint64)')" \
  3 "immutable salt holds after touch"
got_who2="$("$cast" call --rpc-url "$rpc" "$addr" 'whoOf()(address)')"
solana_lean_require_equal "${got_who2,,}" "${sender,,}" "immutable who holds after touch"
got_peer2="$("$cast" call --rpc-url "$rpc" "$addr" 'peerOf()(address)')"
solana_lean_require_equal "${got_peer2,,}" "${peer,,}" "immutable peer holds after touch"

echo "evm-anvil-const: ok (imm u64/address ×2; engineering only)"
