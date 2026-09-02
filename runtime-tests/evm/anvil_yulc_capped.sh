#!/usr/bin/env bash
# Dual-backend Anvil gate: Capped behavior with solc vs yulc bytecode (E-B3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-capped
solana_lean_yulc_or_skip evm-anvil-yulc-capped

out="$root/build/evm-yulc-anvil-capped"
solana_lean_dual_build_program Capped "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-capped

solana_lean_start_anvil "${PF_EVM_PORT:-18591}" "$root/build/evm/anvil-yulc-capped.log"

sender="$("$cast" wallet address --private-key "$private_key")"
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"

run_capped_suite() {
  local label="$1" bytecode="$2"
  local addr
  addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

  solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)' | tr '[:upper:]' '[:lower:]')" \
    "${sender,,}" "$label: ownerOf"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'pausedOf()(uint8)')" \
    0 "$label: initial paused"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'capOf()(uint256)')" \
    100 "$label: cap"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalSupply()(uint256)')" \
    0 "$label: initial supply"

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(uint256)' 40 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalSupply()(uint256)')" \
    40 "$label: owner mint"

  if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
      "$addr" 'mint(uint256)' 1 >/dev/null 2>&1; then
    echo "FAIL: $label non-owner mint unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalSupply()(uint256)')" \
    40 "$label: non-owner holds supply"

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pause()' >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'pausedOf()(uint8)')" \
    1 "$label: paused"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'mint(uint256)' 1 >/dev/null 2>&1; then
    echo "FAIL: $label mint while paused unexpectedly succeeded" >&2
    exit 1
  fi

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'unpause()' >/dev/null
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(uint256)' 60 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalSupply()(uint256)')" \
    100 "$label: mint to cap"
  echo "$addr"
}

solc_addr="$(run_capped_suite solc "$SOLC_HEX")"
yulc_addr="$(run_capped_suite yulc "$YULC_HEX")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'totalSupply()(uint256)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'totalSupply()(uint256)')" \
  "solc vs yulc final totalSupply mismatch"

echo "evm-anvil-yulc-capped: ok (dual-backend behavior match; engineering only)"
