#!/usr/bin/env bash
# Parameterized Lean errors: exact selector/word order for 1, 2, and 4 UInt64 fields, legacy
# zero-field behavior, successful mutation, and revert atomicity.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-typed-errors
bin="$root/build/evm/EvmTypedErrors.bin"
if [[ ! -f "$bin" ]]; then
  lake build Examples.EvmTypedErrors >/dev/null
  lake exe pf -- build --target evm --out "$root/build/evm" EvmTypedErrors >/dev/null
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18688}" "$root/build/evm/anvil-typed-errors.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 3)"

solana_lean_require_storage "$addr" 0 3 "constructor value"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'valueOf()(uint64)')" 3 \
  "initial value"

solana_lean_require_word_revert "$addr" "$sender" \
  "$("$cast" calldata 'update(uint64,uint64)' 5 1)" 'denied(uint64)' \
  "one-field error" 1
solana_lean_require_word_revert "$addr" "$sender" \
  "$("$cast" calldata 'update(uint64,uint64)' 3 7)" 'conflict(uint64,uint64)' \
  "two-field declaration order" 3 3
solana_lean_require_word_revert "$addr" "$sender" \
  "$("$cast" calldata 'update(uint64,uint64)' 5 8)" \
  'exhausted(uint64,uint64,uint64,uint64)' "four-field declaration order" 3 5 8 7
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'update(uint64,uint64)' 0 7)" 'locked()' \
  "zero-field error remains selector-only"

for case in '5 1' '3 7' '5 8' '0 7'; do
  read -r next authorization <<<"$case"
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" \
      'update(uint64,uint64)' "$next" "$authorization" >/dev/null 2>&1; then
    echo "FAIL: update($next,$authorization) unexpectedly succeeded" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 0 3 "typed error is atomic"
done

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'update(uint64,uint64)(uint64)' 5 7)" 5 "successful update result"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" \
  'update(uint64,uint64)' 5 7 >/dev/null
solana_lean_require_storage "$addr" 0 5 "successful update persists"

solana_lean_require_word_revert "$addr" "$sender" \
  "$("$cast" calldata 'update(uint64,uint64)' 9 2)" 'denied(uint64)' \
  "post-success error" 2
solana_lean_require_storage "$addr" 0 5 "post-success revert remains atomic"

echo "evm-anvil-typed-errors: ok (1/2/4-word payloads, zero-field regression, exact returndata, atomicity; engineering only)"
