#!/usr/bin/env bash
# Dual-backend Anvil gate: TipJar ETH env/deposit/payout with solc vs yulc (E-B3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-tipjar
solana_lean_yulc_or_skip evm-anvil-yulc-tipjar

out="$root/build/evm-yulc-anvil-tipjar"
solana_lean_dual_build_program TipJar "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-tipjar

solana_lean_start_anvil "${PF_EVM_PORT:-18596}" "$root/build/evm/anvil-yulc-tipjar.log"

run_tipjar_suite() {
  local label="$1" bytecode="$2"
  local addr sender recipient before after want
  addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
  sender="$("$cast" wallet address --private-key "$private_key")"

  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'chainId()(uint64)')" \
    "$chain_id" "$label: chainId"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfBal()(uint256)')" \
    0 "$label: initial balance"

  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 3 \
      "$addr" 'deposit(uint256)' 7 >/dev/null 2>&1; then
    echo "FAIL: $label wrong-value deposit unexpectedly succeeded" >&2
    exit 1
  fi

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 7 \
    "$addr" 'deposit(uint256)' 7 >/dev/null
  solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
    7 "$label: exact deposit"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfBal()(uint256)')" \
    7 "$label: selfBal after deposit"

  recipient="$("$cast" wallet address --private-key 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)"
  before="$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$recipient")")"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'payout(address,uint256)' "$recipient" 3 >/dev/null
  after="$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$recipient")")"
  want="$("$python" -I -S -c "print(int('$before') + 3)")"
  solana_lean_require_equal "$after" "$want" "$label: payout credit"
  solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
    4 "$label: payout debit"

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 2 --data 0x "$addr" >/dev/null
  solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
    6 "$label: receive credit"
  echo "$addr"
}

solc_addr="$(run_tipjar_suite solc "$SOLC_HEX")"
yulc_addr="$(run_tipjar_suite yulc "$YULC_HEX")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'selfBal()(uint256)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'selfBal()(uint256)')" \
  "solc vs yulc final selfBal mismatch"

echo "evm-anvil-yulc-tipjar: ok (dual-backend behavior match; engineering only)"
