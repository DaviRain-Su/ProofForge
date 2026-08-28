#!/usr/bin/env bash
# TwoStepCounter: EVM-SDK-1 Access gates (requireOwner/requireRunning) + two-step
# ownership (one fixed Access.Ownership nominee). Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-twostep-counter
bin="$root/build/evm/TwoStepCounter.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18560}" "$root/build/evm/anvil-twostep-counter.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty TwoStepCounter.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"
# Anvil default account 1 and 2.
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
third_key="0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a"
third="$("$cast" wallet address --private-key "$third_key")"

solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)')" \
  "$sender" "ownerOf after init"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pausedOf()(uint8)')" \
  0 "initial paused"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  0 "initial count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$third")" \
  0 "no initial nomination"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'bump(uint64)' 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  5 "owner bump"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-owner bump unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'bump(uint64)' 1)" "$other" \
  "non-owner bump"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  5 "non-owner bump holds count"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'pause()' >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pausedOf()(uint8)')" \
  1 "paused after pause"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: bump while paused unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_paused "$addr" "$sender" \
  "$("$cast" calldata 'bump(uint64)' 1)" \
  "bump while paused"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'unpause()' >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pausedOf()(uint8)')" \
  0 "unpaused"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transferOwnership(address)' "$other" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$other")" \
  1 "first nomination recorded"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transferOwnership(address)' "$third" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$other")" \
  0 "replacement invalidates stale nominee"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$third")" \
  1 "replacement nomination recorded"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)')" \
  "$sender" "owner unchanged until accept"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'acceptOwnership()' >/dev/null 2>&1; then
  echo "FAIL: stale nominee acceptOwnership unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'acceptOwnership()')" "$other" \
  "stale nominee acceptOwnership"

"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'acceptOwnership()' >/dev/null
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)')" \
  "$third" "owner rotated to nominee"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$third")" \
  0 "nomination consumed"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: old-owner bump unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'bump(uint64)' 1)" "$sender" \
  "old-owner bump"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  5 "old-owner bump holds count"

"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'bump(uint64)' 2 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  7 "new-owner bump"

# cancel path: new owner nominates sender, cancels, sender cannot accept.
"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'transferOwnership(address)' "$sender" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$sender")" \
  1 "second nomination recorded"
"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'cancelOwnership(address)' "$sender" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pendingOf(address)(uint64)' "$sender")" \
  0 "nomination cancelled"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'acceptOwnership()' >/dev/null 2>&1; then
  echo "FAIL: cancelled acceptOwnership unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'acceptOwnership()')" "$sender" \
  "cancelled acceptOwnership"

# zero-address nomination reverts.
if "$cast" send --rpc-url "$rpc" --private-key "$third_key" \
    "$addr" 'transferOwnership(address)' \
    0x0000000000000000000000000000000000000000 >/dev/null 2>&1; then
  echo "FAIL: zero-address transferOwnership unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$third" \
  "$("$cast" calldata 'transferOwnership(address)' \
    0x0000000000000000000000000000000000000000)" \
  "zero-address transferOwnership"

echo "evm-anvil-twostep-counter: ok (Access gates + two-step ownership; engineering only)"
