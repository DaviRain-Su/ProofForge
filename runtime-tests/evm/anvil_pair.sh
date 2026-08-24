#!/usr/bin/env bash
# Pair multi-slot Anvil gate. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-pair
UINT64_MAX="18446744073709551615"
bin="$root/build/evm/Pair.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18548}" "$root/build/evm/anvil-pair.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Pair.bin" >&2; exit 1; }

require_pair() {
  local addr="$1" left="$2" right="$3" label="$4"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getLeft()(uint64)')" \
    "$left" "$label getLeft"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getRight()(uint64)')" \
    "$right" "$label getRight"
  solana_lean_require_storage "$addr" 0 "$left" "$label storage left"
  solana_lean_require_storage "$addr" 1 "$right" "$label storage right"
}

addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"
require_pair "$addr" 7 0 "constructor"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'initBoth(uint64,uint64)' 5 99 >/dev/null 2>&1; then
  echo "FAIL: alternate initializer unexpectedly exposed at runtime" >&2
  exit 1
fi
require_pair "$addr" 7 0 "rejected initBoth"

simulated="$("$cast" call --rpc-url "$rpc" "$addr" 'creditLeft(uint64)(uint64)' 3)"
solana_lean_require_uint "$simulated" 10 "creditLeft return"
require_pair "$addr" 7 0 "eth_call creditLeft must not commit"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'creditLeft(uint64)' 3 >/dev/null
require_pair "$addr" 10 0 "creditLeft"

max_addr="$(solana_lean_deploy_ctor_u64 "$bytecode" "$UINT64_MAX")"
require_pair "$max_addr" "$UINT64_MAX" 0 "max constructor"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$max_addr" 'creditLeft(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: overflow creditLeft unexpectedly succeeded" >&2
  exit 1
fi
require_pair "$max_addr" "$UINT64_MAX" 0 "overflow hold"

echo "evm-anvil-pair: ok (ctor/initBoth-rejected/creditLeft/right-hold; engineering only)"
