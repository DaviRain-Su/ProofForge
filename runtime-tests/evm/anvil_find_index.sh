#!/usr/bin/env bash
# Typed first-match Option over canonical adjacent bounded bytes/String ABI tails.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-find-index
bin="$root/build/evm/EvmFindIndex.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18583}" "$root/build/evm/anvil-find-index.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

packed_pair_data() {
  local signature="$1"
  local left="$2"
  local right="$3"
  local first_offset="${4:-64}"
  local second_offset="${5:-}"
  local selector
  selector="$("$cast" sig "$signature")"
  "$python" -I -S -c \
    "import sys
left = bytes.fromhex(sys.argv[2])
right = bytes.fromhex(sys.argv[3])
pad = lambda value: value + bytes((-len(value)) % 32)
left_tail = bytes.fromhex(f'{len(left):064x}') + pad(left)
right_tail = bytes.fromhex(f'{len(right):064x}') + pad(right)
first = int(sys.argv[4])
second = int(sys.argv[5]) if sys.argv[5] else 64 + len(left_tail)
print(sys.argv[1] + f'{first:064x}{second:064x}' + left_tail.hex() + right_tail.hex())" \
    "$selector" "$left" "$right" "$first_offset" "$second_offset"
}

require_option_result() {
  local signature="$1"
  local left="$2"
  local right="$3"
  local present="$4"
  local value="$5"
  local result expected
  result="$("$cast" call --rpc-url "$rpc" "$addr" \
    --data "$(packed_pair_data "$signature" "$left" "$right")")"
  expected="$("$python" -I -S -c \
    "import sys; print('0x' + f'{int(sys.argv[1]):064x}{int(sys.argv[2]):064x}')" \
    "$present" "$value")"
  solana_lean_require_equal "$result" "$expected" "bounded first-position $signature"
}

for case in \
  'bytesFindIndex(bytes,bytes)|||1|0' \
  'bytesFindIndex(bytes,bytes)|616263||1|0' \
  'bytesFindIndex(bytes,bytes)|616263|6263|1|1' \
  'bytesFindIndex(bytes,bytes)|616161|6161|1|0' \
  'bytesFindIndex(bytes,bytes)|616263|6163|0|0' \
  'bytesFindIndex(bytes,bytes)|61|6162|0|0' \
  'stringsFindIndex(string,string)|61c2a2|c2a2|1|1' \
  'stringsFindIndex(string,string)|e282ac|c2a2|0|0'; do
  signature="${case%%|*}"
  rest="${case#*|}"
  left="${rest%%|*}"
  rest="${rest#*|}"
  right="${rest%%|*}"
  rest="${rest#*|}"
  present="${rest%%|*}"
  value="${rest#*|}"
  require_option_result "$signature" "$left" "$right" "$present" "$value"
done

for signature in 'bytesFindIndex(bytes,bytes)' 'stringsFindIndex(string,string)'; do
  for malformed in \
    "$(packed_pair_data "$signature" 616263 62 96)" \
    "$(packed_pair_data "$signature" 616263 62 64 64)" \
    "$(packed_pair_data "$signature" 616263 62 64 160)"; do
    if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
      echo "FAIL: noncanonical first-position ABI offsets unexpectedly succeeded" >&2
      exit 1
    fi
  done
done

for invalid_pair in 'c080|616263' '616263|eda080'; do
  left="${invalid_pair%%|*}"
  right="${invalid_pair#*|}"
  malformed="$(packed_pair_data 'stringsFindIndex(string,string)' "$left" "$right")"
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: invalid UTF-8 first-position input unexpectedly succeeded" >&2
    exit 1
  fi
done

echo "evm-anvil-find-index: ok (typed Option, UTF-8 byte offsets, canonical dual tails)"
