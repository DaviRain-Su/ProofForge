#!/usr/bin/env bash
# Reusable reentrancy policy: normal CALL, hostile nested callback, and failed-CALL rollback.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-reentrancy
bin="$root/build/evm/GuardedPayout.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18566}" "$root/build/evm/anvil-reentrancy.log"

solc_bin=""
for candidate in /opt/homebrew/bin/solc /usr/local/bin/solc solc; do
  if command -v "$candidate" >/dev/null 2>&1 || [[ -x "$candidate" ]]; then
    solc_bin="$candidate"
    break
  fi
done
if [[ -z "$solc_bin" ]]; then
  echo "evm-anvil-reentrancy: skip: solc not found" >&2
  exit 0
fi

attacker_out="$root/build/evm/ReentrancyAttacker.bin"
"$solc_bin" --bin --optimize --overwrite -o "$root/build/evm" \
  "$here/ReentrancyAttacker.sol" >/dev/null
[[ -f "$attacker_out" ]] || { echo "FAIL: missing ReentrancyAttacker.bin" >&2; exit 1; }

bytecode="$(tr -d '\n\r ' < "$bin")"
target="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
recipient="0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC"
solana_lean_require_storage "$target" 0 1 "constructor initializes not-entered"

# Ordinary external call succeeds and restores the guard.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$target" 'payout(address,uint256)' "$recipient" 0 >/dev/null
solana_lean_require_storage "$target" 0 1 "normal payout restores guard"

attacker_hex="$(tr -d '\n\r ' < "$attacker_out")"
attacker_receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  --create "0x$attacker_hex")"
attacker="$(printf '%s' "$attacker_receipt" | solana_lean_contract_address)"

# The outer payout succeeds because the attacker catches the nested revert. During the callback,
# the entered sentinel is observable and the nested guarded payout must fail.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$attacker" 'attack(address)' "$target" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$attacker" 'callbacks()(uint256)')" \
  1 "hostile callback count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$attacker" 'observedStatus()(uint256)')" \
  2 "entered sentinel visible during callback"
solana_lean_require_equal \
  "$("$cast" call --rpc-url "$rpc" "$attacker" 'nestedSucceeded()(bool)')" false \
  "nested guarded payout must revert"
solana_lean_require_storage "$target" 0 1 "hostile outer call restores guard"

# A failed value CALL reverts the preceding entered write with the whole transaction.
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$target" 'payout(address,uint256)' "$recipient" 1 >/dev/null 2>&1; then
  echo "FAIL: unfunded guarded payout unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$target" 0 1 "failed CALL rolls back entered sentinel"

echo "evm-anvil-reentrancy: ok (normal/hostile callback/rollback; engineering only)"
