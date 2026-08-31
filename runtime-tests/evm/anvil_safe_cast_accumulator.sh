#!/usr/bin/env bash
# Permissionless UInt256→UInt64 checked accumulation: exact boundary, every discarded-limb class,
# zero, subsequent UInt64 overflow, and storage atomicity across failed transactions.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-safe-cast-accumulator
bin="$root/build/evm/EvmSafeCastAccumulator.bin"
if [[ ! -f "$bin" ]]; then
  lake build Examples.EvmSafeCastAccumulator >/dev/null
  lake exe pf -- build --target evm --out "$root/build/evm" EvmSafeCastAccumulator >/dev/null
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18688}" \
  "$root/build/evm/anvil-safe-cast-accumulator.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

read -r max64 just_over middle_limb high_limb < <("$python" -I -S -c \
  'print(2**64-1, 2**64, 2**128, 2**192)')

solana_lean_require_storage "$addr" 0 0 "constructor total"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint64)')" 0 \
  "initial total"

# Zero is representable and leaves zero state through the successful application branch.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'add(uint256)(uint64)' 0)" 0 "zero cast"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'add(uint256)' 0 >/dev/null
solana_lean_require_storage "$addr" 0 0 "zero add stores no nonzero value"

# Exact UInt64 max is accepted and persisted.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'add(uint256)(uint64)' "$max64")" "$max64" "exact UInt64 max"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'add(uint256)' "$max64" >/dev/null
solana_lean_require_storage "$addr" 0 "$max64" "exact max persists"

# A second representable unit reaches the application's independent checked-add policy.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'add(uint256)' 1)" 'sumOverflow()' "sum overflow after exact max"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'add(uint256)' 1 >/dev/null 2>&1; then
  echo "FAIL: sum overflow unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 "$max64" "sum overflow is atomic"

# Just over UInt64 sets w1. Independent probes set w2 and the highest discarded limb w3.
for case in \
  "$just_over|just-overflow w1" \
  "$middle_limb|middle-limb overflow w2" \
  "$high_limb|high-limb overflow w3"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'add(uint256)' "$value")" 'amountTooWide()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'add(uint256)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 0 "$max64" "$label is atomic"
done

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint64)')" \
  "$max64" "all failed transactions preserve the exact max"

echo "evm-anvil-safe-cast-accumulator: ok (zero + exact max + checked-add overflow + w1/w2/w3 rejection + atomicity; engineering only)"
