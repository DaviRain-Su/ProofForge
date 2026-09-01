#!/usr/bin/env bash
# Allocation-free bounded bytes/String search over canonical adjacent ABI tails.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-search
bin="$root/build/evm/EvmSearch.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18582}" "$root/build/evm/anvil-search.log"

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

for case in \
  'bytesContains(bytes,bytes)|||1' \
  'bytesContains(bytes,bytes)||61|0' \
  'bytesContains(bytes,bytes)|616263||1' \
  'bytesContains(bytes,bytes)|616263|62|1' \
  'bytesContains(bytes,bytes)|616263|6263|1' \
  'bytesContains(bytes,bytes)|616263|6163|0' \
  'stringsContains(string,string)|e282ac|e282ac|1' \
  'stringsContains(string,string)|e282ac|c2a2|0' \
  'bytesStartsWith(bytes,bytes)|||1' \
  'bytesStartsWith(bytes,bytes)||61|0' \
  'bytesStartsWith(bytes,bytes)|616263||1' \
  'bytesStartsWith(bytes,bytes)|616263|6162|1' \
  'bytesStartsWith(bytes,bytes)|616263|6263|0' \
  'bytesStartsWith(bytes,bytes)|616263|616263|1' \
  'bytesEndsWith(bytes,bytes)|||1' \
  'bytesEndsWith(bytes,bytes)||61|0' \
  'bytesEndsWith(bytes,bytes)|616263||1' \
  'bytesEndsWith(bytes,bytes)|616263|6263|1' \
  'bytesEndsWith(bytes,bytes)|616263|6162|0' \
  'bytesEndsWith(bytes,bytes)|616263|616263|1' \
  'stringsStartsWith(string,string)|e282ac|e282ac|1' \
  'stringsStartsWith(string,string)|e282ac|c2a2|0' \
  'stringsEndsWith(string,string)|e282ac|e282ac|1' \
  'stringsEndsWith(string,string)|e282ac|c2a2|0'; do
  signature="${case%%|*}"
  rest="${case#*|}"
  left="${rest%%|*}"
  rest="${rest#*|}"
  right="${rest%%|*}"
  expected="${rest#*|}"
  result="$("$cast" call --rpc-url "$rpc" "$addr" \
    --data "$(packed_pair_data "$signature" "$left" "$right")")"
  solana_lean_require_uint "$result" "$expected" "bounded search $signature"
done

for signature in \
  'bytesContains(bytes,bytes)' 'stringsContains(string,string)' \
  'bytesStartsWith(bytes,bytes)' 'stringsStartsWith(string,string)' \
  'bytesEndsWith(bytes,bytes)' 'stringsEndsWith(string,string)'; do
  for malformed in \
    "$(packed_pair_data "$signature" 616263 62 96)" \
    "$(packed_pair_data "$signature" 616263 62 64 64)" \
    "$(packed_pair_data "$signature" 616263 62 64 160)"; do
    if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
      echo "FAIL: noncanonical bounded-search ABI offsets unexpectedly succeeded" >&2
      exit 1
    fi
  done
done

for signature in 'stringsContains(string,string)' \
  'stringsStartsWith(string,string)' 'stringsEndsWith(string,string)'; do
  for invalid_pair in 'c080|616263' '616263|eda080'; do
    left="${invalid_pair%%|*}"
    right="${invalid_pair#*|}"
    malformed="$(packed_pair_data "$signature" "$left" "$right")"
    if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
      echo "FAIL: invalid UTF-8 bounded-search input unexpectedly succeeded" >&2
      exit 1
    fi
  done
done

echo "evm-anvil-search: ok (contains/prefix/suffix, UTF-8, canonical dual tails)"
