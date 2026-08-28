#!/usr/bin/env bash
# Bounded Array v1: canonical dynamic offsets/tails with a fixed source-local frame.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-bounded
bin="$root/build/evm/EvmBounded.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18562}" "$root/build/evm/anvil-bounded.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

empty="$("$cast" call --rpc-url "$rpc" "$addr" \
  'boundedValues(uint64[])(uint64)' '[]')"
solana_lean_require_uint "$empty" 0 "empty bounded array"

short="$("$cast" call --rpc-url "$rpc" "$addr" \
  'boundedValues(uint64[])(uint64)' '[11,13]')"
solana_lean_require_uint "$short" 13 "inactive bounded slots are zero"

full="$("$cast" call --rpc-url "$rpc" "$addr" \
  'boundedValues(uint64[])(uint64)' '[11,13,17,19]')"
solana_lean_require_uint "$full" 34 "full bounded array"

combined="$("$cast" call --rpc-url "$rpc" "$addr" \
  'combine(uint32,uint64[],bool,uint16[])(uint64)' 7 '[11,13]' true '[17,19,23]')"
solana_lean_require_uint "$combined" 49 "multiple canonical dynamic tails"

selector="$("$cast" sig 'boundedValues(uint64[])')"
array_data() {
  "$python" -I -S -c \
    "import sys; print(sys.argv[1] + ''.join(f'{int(v):064x}' for v in sys.argv[2:]))" \
    "$selector" "$@"
}

# Wrong head offsets, over-capacity length, short/trailing tails, and noncanonical uint64 words
# must all fail closed. Standard ABI offsets are relative to the argument block after the selector.
for malformed in \
  "$(array_data 0 2 11 13)" \
  "$(array_data 64 2 11 13)" \
  "$(array_data 32 5 1 2 3 4 5)" \
  "$(array_data 32 2 11)" \
  "$(array_data 32 1 11 0)" \
  "$(array_data 32 1 18446744073709551616)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: malformed bounded dynamic ABI calldata unexpectedly succeeded" >&2
    exit 1
  fi
done

combine_selector="$("$cast" sig 'combine(uint32,uint64[],bool,uint16[])')"
combine_data() {
  "$python" -I -S -c \
    "import sys; print(sys.argv[1] + ''.join(f'{int(v):064x}' for v in sys.argv[2:]))" \
    "$combine_selector" "$@"
}

# The second dynamic tail must begin immediately after the first one: head=128 bytes,
# left tail=96 bytes, so right's canonical offset is 224 rather than an alias or a gap.
for malformed in \
  "$(combine_data 7 128 1 128 2 11 13 3 17 19 23)" \
  "$(combine_data 7 128 1 256 2 11 13 3 17 19 23)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: noncanonical later bounded ABI offset unexpectedly succeeded" >&2
    exit 1
  fi
done

echo "evm-anvil-bounded: ok (canonical offset/length/tail/padding matrix; engineering only)"
