#!/usr/bin/env bash
# Credits: EVM-SDK-1 second independent Access consumer — owner-granted credit ledger
# reusing requireOwner/requireRunning and Access.Ownership two-step transfer. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-credits
bin="$root/build/evm/Credits.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18561}" "$root/build/evm/anvil-credits.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Credits.bin" >&2; exit 1; }

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
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  0 "initial total"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$other")" \
  0 "no initial credit"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grant(address,uint256)' "$other" 7 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$other")" \
  7 "owner grant"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'grant(address,uint256)' "$other" 1 >/dev/null 2>&1; then
  echo "FAIL: non-owner grant unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'grant(address,uint256)' "$other" 1)" "$other" \
  "non-owner grant"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$other")" \
  7 "non-owner grant holds credit"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'pause()' >/dev/null
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'grant(address,uint256)' "$other" 1 >/dev/null 2>&1; then
  echo "FAIL: grant while paused unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_paused "$addr" "$sender" \
  "$("$cast" calldata 'grant(address,uint256)' "$other" 1)" \
  "grant while paused"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'claim(uint256)' 1 >/dev/null 2>&1; then
  echo "FAIL: claim while paused unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_paused "$addr" "$other" \
  "$("$cast" calldata 'claim(uint256)' 1)" \
  "claim while paused"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'unpause()' >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'pausedOf()(uint8)')" \
  0 "unpaused"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'claim(uint256)' 7 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  7 "claim moves credit into total"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$other")" \
  0 "claim debits credit"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'claim(uint256)' 1 >/dev/null 2>&1; then
  echo "FAIL: over-credit claim unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$other" \
  "$("$cast" calldata 'claim(uint256)' 1)" 0 1 \
  "over-credit claim"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  7 "over-credit claim holds total"

# Two-step rotation replaces the sole pending address; a stale nominee cannot accept.
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
    "$addr" 'grant(address,uint256)' "$other" 1 >/dev/null 2>&1; then
  echo "FAIL: old-owner grant unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'grant(address,uint256)' "$other" 1)" "$sender" \
  "old-owner grant"

"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'grant(address,uint256)' "$third" 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$third")" \
  5 "new-owner grant"
"$cast" send --rpc-url "$rpc" --private-key "$third_key" \
  "$addr" 'claim(uint256)' 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint256)')" \
  12 "new-owner claim accumulates"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'creditOf(address)(uint256)' "$third")" \
  0 "new-owner claim debits credit"

echo "evm-anvil-credits: ok (Access reuse, second consumer; engineering only)"
