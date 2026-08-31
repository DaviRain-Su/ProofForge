#!/usr/bin/env bash
# Permissionless UInt256→UInt64 accumulation plus UInt256→UInt32/UInt16/UInt8 replacement: exact
# boundaries, every discarded-limb/low-word class, application errors, and storage atomicity.
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

read -r max8 just_over8 max16 just_over16 max32 just_over32 max64 just_over \
    middle_limb high_limb < <( \
  "$python" -I -S -c \
    'print(2**8-1, 2**8, 2**16-1, 2**16, 2**32-1, 2**32, 2**64-1, 2**64, 2**128, 2**192)'
)

solana_lean_require_storage "$addr" 0 0 "constructor total"
solana_lean_require_storage "$addr" 1 1 "constructor checkpoint"
solana_lean_require_storage "$addr" 2 2 "constructor batch"
solana_lean_require_storage "$addr" 3 3 "constructor mode"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'totalOf()(uint64)')" 0 \
  "initial total"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'checkpointOf()(uint32)')" 1 "initial checkpoint"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'batchOf()(uint16)')" 2 "initial batch"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'modeOf()(uint8)')" 3 "initial mode"

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

# UInt32 has a second discarded-bit boundary inside w0. Zero reaches the application policy;
# exact max is persisted, while 2^32 and every upper-limb class fail before the checkpoint write.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'setCheckpoint(uint256)' 0)" 'checkpointZero()' "zero checkpoint"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setCheckpoint(uint256)' 0 >/dev/null 2>&1; then
  echo "FAIL: zero checkpoint unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 1 1 "zero checkpoint is atomic"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'setCheckpoint(uint256)(uint32)' "$max32")" "$max32" "exact UInt32 max"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setCheckpoint(uint256)' "$max32" >/dev/null
solana_lean_require_storage "$addr" 1 "$max32" "exact UInt32 max persists"

for case in \
  "$just_over32|low-word upper-bit overflow" \
  "$just_over|checkpoint w1 overflow" \
  "$middle_limb|checkpoint w2 overflow" \
  "$high_limb|checkpoint w3 overflow"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'setCheckpoint(uint256)' "$value")" 'checkpointTooWide()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setCheckpoint(uint256)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 1 "$max32" "$label is atomic"
done
solana_lean_require_storage "$addr" 0 "$max64" "checkpoint path preserves UInt64 total"

# UInt16 repeats the checked replacement contract at the next narrow scalar boundary. The low-word
# 2^16 bit and every upper UInt256 limb must fail before the batch slot can change.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'setBatch(uint256)' 0)" 'batchZero()' "zero batch"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setBatch(uint256)' 0 >/dev/null 2>&1; then
  echo "FAIL: zero batch unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 2 2 "zero batch is atomic"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'setBatch(uint256)(uint16)' "$max16")" "$max16" "exact UInt16 max"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setBatch(uint256)' "$max16" >/dev/null
solana_lean_require_storage "$addr" 2 "$max16" "exact UInt16 max persists"

for case in \
  "$just_over16|batch low-word upper-bit overflow" \
  "$just_over|batch w1 overflow" \
  "$middle_limb|batch w2 overflow" \
  "$high_limb|batch w3 overflow"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'setBatch(uint256)' "$value")" 'batchTooWide()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setBatch(uint256)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 2 "$max16" "$label is atomic"
done
solana_lean_require_storage "$addr" 0 "$max64" "batch path preserves UInt64 total"
solana_lean_require_storage "$addr" 1 "$max32" "batch path preserves UInt32 checkpoint"

# UInt8 closes the unsigned fixed-scalar narrowing surface. The first ninth-bit value and every
# upper UInt256 limb fail before the mode slot can change.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'setMode(uint256)' 0)" 'modeZero()' "zero mode"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setMode(uint256)' 0 >/dev/null 2>&1; then
  echo "FAIL: zero mode unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 3 "zero mode is atomic"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'setMode(uint256)(uint8)' "$max8")" "$max8" "exact UInt8 max"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setMode(uint256)' "$max8" >/dev/null
solana_lean_require_storage "$addr" 3 "$max8" "exact UInt8 max persists"

for case in \
  "$just_over8|mode low-word upper-bit overflow" \
  "$just_over|mode w1 overflow" \
  "$middle_limb|mode w2 overflow" \
  "$high_limb|mode w3 overflow"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'setMode(uint256)' "$value")" 'modeTooWide()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setMode(uint256)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 3 "$max8" "$label is atomic"
done
solana_lean_require_storage "$addr" 0 "$max64" "mode path preserves UInt64 total"
solana_lean_require_storage "$addr" 1 "$max32" "mode path preserves UInt32 checkpoint"
solana_lean_require_storage "$addr" 2 "$max16" "mode path preserves UInt16 batch"

echo "evm-anvil-safe-cast-accumulator: ok (UInt64/UInt32/UInt16/UInt8 boundaries, all discarded bits, application policy, atomicity; engineering only)"
