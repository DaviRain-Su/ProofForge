#!/usr/bin/env bash
# Owner-gated UInt128→UInt64 checked replacement: zero policy, exact boundary, just/high-limb
# overflow, authorization ordering, and storage atomicity across all rejected transactions.
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

read -r max64 just_over high_limb < <("$python" -I -S -c \
  'print(2**64-1, 2**64, 2**127)')

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'limitOf()(uint64)')" 7 \
  "constructor limit"
solana_lean_require_storage "$addr" 3 7 "constructor limit slot"

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

echo "evm-anvil-safe-cast-config: ok (owner + zero policy + exact max + just/high-limb rejection + atomicity; engineering only)"
