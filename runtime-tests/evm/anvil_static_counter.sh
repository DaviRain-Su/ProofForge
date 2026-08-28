#!/usr/bin/env bash
# EvmStaticCounter: static scalar/wide/record layout and immutable-owner policy.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-static-counter
bin="$root/build/evm/EvmStaticCounter.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18563}" "$root/build/evm/anvil-static-counter.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
encoded="$("$cast" abi-encode 'constructor(uint64,address)' 7 "$sender")"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  --create "0x${bytecode}${encoded#0x}")"
addr="$(printf '%s' "$receipt" | solana_lean_contract_address)"

# Declaration order is paused@0, total_w0..w3@1..4, tally.count@5, tally.window@6.
solana_lean_require_storage "$addr" 0 0 "constructor paused"
solana_lean_require_storage "$addr" 1 7 "constructor total.w0"
for slot in 2 3 4 5 6; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero neighbor"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  7 "constructor total getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'countOf()(uint64)')" \
  0 "constructor count getter"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'bump(uint64)' 5 >/dev/null
solana_lean_require_storage "$addr" 1 12 "wide total targeted mutation"
for slot in 2 3 4; do
  solana_lean_require_storage "$addr" "$slot" 0 "wide high limb remains zero"
done
solana_lean_require_storage "$addr" 5 5 "record count targeted mutation"
solana_lean_require_storage "$addr" 6 0 "record window neighbor remains zero"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  12 "wide total after bump"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'countOf()(uint64)')" \
  5 "record count after bump"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setWindow(uint16)' 513 >/dev/null
solana_lean_require_storage "$addr" 6 513 "record window targeted mutation"
solana_lean_require_storage "$addr" 5 5 "record count neighbor holds"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setWindow(uint16)' 9)" "$other" "non-owner window update"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setWindow(uint16)' 9 >/dev/null 2>&1; then
  echo "FAIL: non-owner window update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 6 513 "unauthorized update holds window"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'pause()' >/dev/null
solana_lean_require_storage "$addr" 0 1 "paused flag"
solana_lean_require_paused "$addr" "$sender" \
  "$("$cast" calldata 'bump(uint64)' 1)" "paused bump"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: paused bump unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 1 12 "paused bump holds total"
solana_lean_require_storage "$addr" 5 5 "paused bump holds count"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'unpause()' >/dev/null
solana_lean_require_storage "$addr" 0 0 "unpaused flag"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'windowOf()(uint16)')" \
  513 "record window getter"

echo "evm-anvil-static-counter: ok (scalar/wide/record slots + access gates; engineering only)"
