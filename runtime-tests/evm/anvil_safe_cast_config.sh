#!/usr/bin/env bash
# Owner-gated UInt128→UInt64/UInt32 checked replacement: independent zero policies, exact
# boundaries, low-word/upper-limb overflow, authorization ordering, and storage atomicity.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-safe-cast-config
bin="$root/build/evm/EvmSafeCastConfig.bin"
if [[ ! -f "$bin" ]]; then
  lake build Examples.EvmSafeCastConfig >/dev/null
  lake exe pf -- build --target evm --out "$root/build/evm" EvmSafeCastConfig >/dev/null
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18689}" "$root/build/evm/anvil-safe-cast-config.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

read -r max32 just_over32 max64 just_over high_limb < <("$python" -I -S -c \
  'print(2**32-1, 2**32, 2**64-1, 2**64, 2**127)')

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'limitOf()(uint64)')" 7 \
  "constructor limit"
solana_lean_require_storage "$addr" 3 7 "constructor limit slot"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'windowOf()(uint32)')" 3 \
  "constructor window"
solana_lean_require_storage "$addr" 4 3 "constructor window slot"

# Zero is representable, but this application's independent nonzero policy rejects it.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'setLimit(uint128)' 0)" 'zero()' "zero limit"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setLimit(uint128)' 0 >/dev/null 2>&1; then
  echo "FAIL: zero limit unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 7 "zero rejection is atomic"

# Exact UInt64 max is accepted and replaces the prior limit.
solana_lean_require_uint "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'setLimit(uint128)(uint64)' "$max64")" "$max64" "exact UInt64 max"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setLimit(uint128)' "$max64" >/dev/null
solana_lean_require_storage "$addr" 3 "$max64" "exact max persists"

# UInt128 just-overflow and a distant high-limb value both fail before the literal limit write.
for case in "$just_over|just-overflow" "$high_limb|high-limb overflow"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'setLimit(uint128)' "$value")" 'invalidLimit()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setLimit(uint128)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 3 "$max64" "$label is atomic"
done

# Authorization is a distinct outer policy and runs before narrowing or state publication.
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setLimit(uint128)' 9)" "$other" "non-admin representable limit"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setLimit(uint128)' 9 >/dev/null 2>&1; then
  echo "FAIL: non-admin limit update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setLimit(uint128)' "$just_over")" "$other" \
  "non-admin wide input reaches authorization first"
solana_lean_require_storage "$addr" 3 "$max64" "unauthorized updates are atomic"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'limitOf()(uint64)')" \
  "$max64" "all rejected transactions preserve the exact max"

# The same owner policy independently consumes UInt128→UInt32. The 32-bit boundary checks both
# high bits inside w0 and the complete w1 limb before the `window` slot can change.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'setWindow(uint128)' 0)" 'windowZero()' "zero window"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setWindow(uint128)' 0 >/dev/null 2>&1; then
  echo "FAIL: zero window unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 4 3 "zero window is atomic"

solana_lean_require_uint "$("$cast" call --from "$sender" --rpc-url "$rpc" "$addr" \
  'setWindow(uint128)(uint32)' "$max32")" "$max32" "exact UInt32 max window"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setWindow(uint128)' "$max32" >/dev/null
solana_lean_require_storage "$addr" 4 "$max32" "exact UInt32 max window persists"

for case in \
  "$just_over32|window low-word upper-bit overflow" \
  "$just_over|window w1 overflow" \
  "$high_limb|window distant high-bit overflow"; do
  value="${case%%|*}"
  label="${case#*|}"
  solana_lean_require_named_revert "$addr" "$sender" \
    "$("$cast" calldata 'setWindow(uint128)' "$value")" 'invalidWindow()' "$label"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setWindow(uint128)' "$value" >/dev/null 2>&1; then
    echo "FAIL: $label unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 4 "$max32" "$label is atomic"
done

solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setWindow(uint128)' 11)" "$other" "non-admin representable window"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setWindow(uint128)' 11 >/dev/null 2>&1; then
  echo "FAIL: non-admin window update unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setWindow(uint128)' "$just_over32")" "$other" \
  "non-admin UInt32 overflow reaches authorization first"
solana_lean_require_storage "$addr" 4 "$max32" "unauthorized window updates are atomic"
solana_lean_require_storage "$addr" 3 "$max64" "window path preserves UInt64 limit"

echo "evm-anvil-safe-cast-config: ok (owner + UInt64/UInt32 boundaries + application policy + atomicity; engineering only)"
