#!/usr/bin/env bash
# Dual-backend Anvil gate: Const immutables with solc vs yulc bytecode (E-B3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-const
solana_lean_yulc_or_skip evm-anvil-yulc-const

out="$root/build/evm-yulc-anvil-const"
solana_lean_dual_build_program Const "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-const

solana_lean_start_anvil "${PF_EVM_PORT:-18592}" "$root/build/evm/anvil-yulc-const.log"

sender="$("$cast" wallet address --private-key "$private_key")"
peer="$("$cast" wallet address --private-key 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)"
encoded="$("$cast" abi-encode 'constructor(uint64,uint64,address,address)' 7 3 "$sender" "$peer")"

run_const_suite() {
  local label="$1" bytecode="$2"
  local addr receipt
  receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
    --create "0x${bytecode}${encoded#0x}")"
  addr="$(printf '%s' "$receipt" | solana_lean_contract_address)"

  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'seedOf()(uint64)')" \
    7 "$label: immutable seed"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'saltOf()(uint64)')" \
    3 "$label: immutable salt"
  solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'whoOf()(address)' | tr '[:upper:]' '[:lower:]')" \
    "${sender,,}" "$label: immutable who"
  solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'peerOf()(address)' | tr '[:upper:]' '[:lower:]')" \
    "${peer,,}" "$label: immutable peer"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    0 "$label: dummy starts at 0"

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'touch(uint64)' 11 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    11 "$label: dummy after touch"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'seedOf()(uint64)')" \
    7 "$label: seed holds after touch"
  echo "$addr"
}

solc_addr="$(run_const_suite solc "$SOLC_HEX")"
yulc_addr="$(run_const_suite yulc "$YULC_HEX")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'get()(uint64)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'get()(uint64)')" \
  "solc vs yulc final get() mismatch"

echo "evm-anvil-yulc-const: ok (dual-backend behavior match; engineering only)"
