#!/usr/bin/env bash
# Bounded dynamic ABI: canonical array/packed-byte tails with fixed source-local frames.
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

packed_data() {
  local signature="$1"
  local hex_bytes="$2"
  local packed_selector
  packed_selector="$("$cast" sig "$signature")"
  "$python" -I -S -c \
    "import sys
payload = bytes.fromhex(sys.argv[2])
padding = bytes((-len(payload)) % 32)
print(sys.argv[1] + f'{32:064x}{len(payload):064x}' + (payload + padding).hex())" \
    "$packed_selector" "$hex_bytes"
}

call_packed() {
  local signature="$1"
  local hex_bytes="$2"
  "$cast" call --rpc-url "$rpc" "$addr" --data "$(packed_data "$signature" "$hex_bytes")"
}

require_cast_json() {
  local signature="$1"
  local input="$2"
  local expected="$3"
  local message="$4"
  local actual
  actual="$("$cast" call --json --rpc-url "$rpc" "$addr" "$signature" "$input")"
  "$python" -I -S -c \
    "import json, sys
actual = json.loads(sys.argv[1])
expected = json.loads(sys.argv[2])
if actual != expected:
    print(f\"FAIL: {sys.argv[3]} (expected {expected!r}, got {actual!r})\", file=sys.stderr)
    raise SystemExit(1)" \
    "$actual" "$expected" "$message"
}

packed_pair_data() {
  local signature="$1"
  local left="$2"
  local right="$3"
  local first_offset="${4:-64}"
  local second_offset="${5:-}"
  local packed_selector
  packed_selector="$("$cast" sig "$signature")"
  "$python" -I -S -c \
    "import sys
left = bytes.fromhex(sys.argv[2])
right = bytes.fromhex(sys.argv[3])
pad = lambda value: value + bytes((-len(value)) % 32)
tail_left = bytes.fromhex(f'{len(left):064x}') + pad(left)
tail_right = bytes.fromhex(f'{len(right):064x}') + pad(right)
first = int(sys.argv[4])
second = int(sys.argv[5]) if sys.argv[5] else 64 + len(tail_left)
print(sys.argv[1] + f'{first:064x}{second:064x}' + tail_left.hex() + tail_right.hex())" \
    "$packed_selector" "$left" "$right" "$first_offset" "$second_offset"
}

for case in \
  'boundedBytes(bytes)|' \
  'boundedBytes(bytes)|0b0d' \
  'boundedBytes(bytes)|0b0d1113171d1f25'; do
  signature="${case%%|*}"
  hex_bytes="${case#*|}"
  result="$(call_packed "$signature" "$hex_bytes")"
  case "$hex_bytes" in
    '') expected=0 ;;
    0b0d) expected=13 ;;
    *) expected=56 ;;
  esac
  solana_lean_require_uint "$result" "$expected" "canonical packed bytes $hex_bytes"
done

for case in \
  'bytesEqual(bytes,bytes)|616263|616263|1' \
  'bytesEqual(bytes,bytes)|616263|616264|0' \
  'bytesEqual(bytes,bytes)|616263|6162|0' \
  'stringsEqual(string,string)|e282ac|e282ac|1' \
  'stringsEqual(string,string)|c2a2|e282ac|0' \
  'bytesLess(bytes,bytes)|||0' \
  'bytesLess(bytes,bytes)|616263|616264|1' \
  'bytesLess(bytes,bytes)|616264|616263|0' \
  'bytesLess(bytes,bytes)|6162|616263|1' \
  'bytesLess(bytes,bytes)|616263|6162|0' \
  'stringsLess(string,string)|c2a2|e282ac|1' \
  'stringsLess(string,string)|e282ac|c2a2|0'; do
  signature="${case%%|*}"
  rest="${case#*|}"
  left="${rest%%|*}"
  rest="${rest#*|}"
  right="${rest%%|*}"
  expected="${rest#*|}"
  result="$("$cast" call --rpc-url "$rpc" "$addr" \
    --data "$(packed_pair_data "$signature" "$left" "$right")")"
  solana_lean_require_uint "$result" "$expected" "bounded active-prefix comparison $signature"
done

# Both dynamic tails are independently canonical and adjacent. Aliasing, gaps, and wrong first
# offsets fail before either source-level comparison observes its fixed local frames.
for signature in 'bytesEqual(bytes,bytes)' 'bytesLess(bytes,bytes)'; do
  for malformed in \
    "$(packed_pair_data "$signature" 616263 616263 96)" \
    "$(packed_pair_data "$signature" 616263 616263 64 64)" \
    "$(packed_pair_data "$signature" 616263 616263 64 160)"; do
    if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
      echo "FAIL: noncanonical bounded comparison ABI offsets unexpectedly succeeded" >&2
      exit 1
    fi
  done
done

for signature in 'stringsEqual(string,string)' 'stringsLess(string,string)'; do
  for invalid_pair in 'c080|616263' '616263|eda080'; do
    left="${invalid_pair%%|*}"
    right="${invalid_pair#*|}"
    malformed="$(packed_pair_data "$signature" "$left" "$right")"
    if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
      echo "FAIL: invalid UTF-8 bounded comparison input unexpectedly succeeded" >&2
      exit 1
    fi
  done
done

for case in \
  '|0' \
  '616263|100' \
  'c2a2|196' \
  'e282ac|229' \
  'f09f92a9|244' \
  '6162636465666768|209'; do
  hex_bytes="${case%%|*}"
  expected="${case#*|}"
  result="$(call_packed 'boundedString(string)' "$hex_bytes")"
  solana_lean_require_uint "$result" "$expected" "strict UTF-8 string $hex_bytes"
done

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

wide_selector="$("$cast" sig 'echoBoundedWide(uint128[])')"
wide_array_data() {
  "$python" -I -S -c \
    "import sys; print(sys.argv[1] + ''.join(f'{int(v):064x}' for v in sys.argv[2:]))" \
    "$wide_selector" "$@"
}

for malformed in \
  "$(wide_array_data 0 2 11 13)" \
  "$(wide_array_data 32 3 1 2 3)" \
  "$(wide_array_data 32 2 11)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: malformed wide bounded dynamic ABI calldata unexpectedly succeeded" >&2
    exit 1
  fi
done

pairs_selector="$("$cast" sig 'echoBoundedPairs((uint64,uint16)[])')"
pairs_array_data() {
  "$python" -I -S -c \
    "import sys
sel = sys.argv[1]
offset = int(sys.argv[2])
length = int(sys.argv[3])
words = [f'{int(v):064x}' for v in sys.argv[4:]]
print(sel + f'{offset:064x}{length:064x}' + ''.join(words))" \
    "$pairs_selector" "$@"
}

for malformed in \
  "$(pairs_array_data 0 1 11 13)" \
  "$(pairs_array_data 32 3 1 2 3 4 5 6)" \
  "$(pairs_array_data 32 2 11 13)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: malformed constructed bounded dynamic ABI calldata unexpectedly succeeded" >&2
    exit 1
  fi
done

for over_capacity in \
  '[1,2,3]' \
  '[(1,2),(3,4),(5,6)]'; do
  signature='echoBoundedWide(uint128[])(uint128[])'
  [[ "$over_capacity" == *"("* ]] && signature='echoBoundedPairs((uint64,uint16)[])((uint64,uint16)[])'
  if "$cast" call --rpc-url "$rpc" "$addr" "$signature" "$over_capacity" >/dev/null 2>&1; then
    echo "FAIL: over-capacity wide/constructed bounded input unexpectedly succeeded" >&2
    exit 1
  fi
done

bytes_selector="$("$cast" sig 'boundedBytes(bytes)')"
malformed_packed_data() {
  "$python" -I -S -c \
    "import sys
s = sys.argv[1]
word = lambda n: f'{n:064x}'
cases = [
  word(0) + word(1) + '0b' + '00' * 31,
  word(64) + word(1) + '0b' + '00' * 31,
  word(32) + word(9) + '01' * 9 + '00' * 23,
  word(32) + word(1),
  word(32) + word(0) + '00' * 32,
  word(32) + word(1) + '0b0d' + '00' * 30,
]
print('\\n'.join(s + case for case in cases))" "$bytes_selector"
}

while IFS= read -r malformed; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: malformed packed bytes ABI calldata unexpectedly succeeded" >&2
    exit 1
  fi
done < <(malformed_packed_data)

for invalid_utf8 in \
  80 \
  c080 \
  e08080 \
  eda080 \
  e282 \
  f4908080 \
  f5808080; do
  malformed="$(packed_data 'boundedString(string)' "$invalid_utf8")"
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: invalid UTF-8 ABI string unexpectedly succeeded ($invalid_utf8)" >&2
    exit 1
  fi
done

# Dynamic results use an output-only codec plan: the fixed source frame is encoded as the exact
# standard-ABI active prefix rather than returned as capacity-sized scalar words.
for case in \
  '[]|[]' \
  '[11,13]|[11, 13]' \
  '[11,13,17,19]|[11, 13, 17, 19]'; do
  input="${case%%|*}"
  expected="${case#*|}"
  echo_array="$("$cast" call --rpc-url "$rpc" "$addr" \
    'echoBoundedValues(uint16[])(uint16[])' "$input")"
  solana_lean_require_equal "$echo_array" "$expected" "bounded array dynamic result $input"
done

# Wide one-ABI-word elements: each uint128 occupies one dynamic tail word at the ABI boundary.
for case in \
  '[]|[[]]' \
  '[11,13]|[[11,13]]' \
  '[340282366920938463463374607431768211455,1]|[["340282366920938463463374607431768211455",1]]'; do
  input="${case%%|*}"
  expected="${case#*|}"
  require_cast_json 'echoBoundedWide(uint128[])(uint128[])' "$input" "$expected" \
    "wide bounded array dynamic result $input"
done

# Constructed static-product elements: each tuple is two adjacent ABI words in the dynamic tail.
for case in \
  '[]|[]' \
  '[(11,13)]|[(11, 13)]' \
  '[(11,13),(17,19)]|[(11, 13), (17, 19)]'; do
  input="${case%%|*}"
  expected="${case#*|}"
  echo_pairs="$("$cast" call --rpc-url "$rpc" "$addr" \
    'echoBoundedPairs((uint64,uint16)[])((uint64,uint16)[])' "$input")"
  solana_lean_require_equal "$echo_pairs" "$expected" "constructed bounded array dynamic result $input"
done

# Tagged-in-array Option elements: each slot is Tagged Tuple v1 (bool,uint64).
options_selector="$("$cast" sig 'echoBoundedOptions((bool,uint64)[])')"
options_array_data() {
  "$python" -I -S -c \
    "import sys
sel = sys.argv[1]
offset = int(sys.argv[2])
length = int(sys.argv[3])
words = [f'{int(v):064x}' for v in sys.argv[4:]]
print(sel + f'{offset:064x}{length:064x}' + ''.join(words))" \
    "$options_selector" "$@"
}

for malformed in \
  "$(options_array_data 0 1 1 11)" \
  "$(options_array_data 32 3 1 1 1 2 1 3)" \
  "$(options_array_data 32 1 1)" \
  "$(options_array_data 32 1 0 11)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: malformed tagged-in-array Option calldata unexpectedly succeeded" >&2
    exit 1
  fi
done

if "$cast" call --rpc-url "$rpc" "$addr" \
    'echoBoundedOptions((bool,uint64)[])((bool,uint64)[])' \
    '[(true,1),(false,0),(true,3)]' >/dev/null 2>&1; then
  echo "FAIL: over-capacity tagged Option array unexpectedly succeeded" >&2
  exit 1
fi

for case in \
  '[]|[]' \
  '[(false,0)]|[(false, 0)]' \
  '[(true,11)]|[(true, 11)]' \
  '[(true,11),(false,0)]|[(true, 11), (false, 0)]' \
  '[(false,0),(true,19)]|[(false, 0), (true, 19)]'; do
  input="${case%%|*}"
  expected="${case#*|}"
  echo_options="$("$cast" call --rpc-url "$rpc" "$addr" \
    'echoBoundedOptions((bool,uint64)[])((bool,uint64)[])' "$input")"
  solana_lean_require_equal "$echo_options" "$expected" "tagged Option array dynamic result $input"
done

for input in 0x 0x0b0d 0x0b0d1113171d1f25; do
  echo_bytes="$("$cast" call --rpc-url "$rpc" "$addr" \
    'echoBoundedBytes(bytes)(bytes)' "$input")"
  solana_lean_require_equal "$echo_bytes" "$input" "bounded bytes dynamic result $input"
done

echo_string="$("$cast" call --rpc-url "$rpc" "$addr" \
  'echoBoundedString(string)(string)' abc)"
solana_lean_require_equal "$echo_string" '"abc"' "bounded string dynamic result"

make_signature='makeBoundedString(uint32,uint8,uint8,uint8,uint8,uint8,uint8,uint8,uint8)(string)'
made_string="$("$cast" call --rpc-url "$rpc" "$addr" "$make_signature" \
  3 97 98 99 0 0 0 0 0)"
solana_lean_require_equal "$made_string" '"abc"' "constructed UTF-8 dynamic result"

# Output capacity and UTF-8 are checked at publication even when no dynamic input decoder ran.
if "$cast" call --rpc-url "$rpc" "$addr" "$make_signature" \
    9 97 98 99 0 0 0 0 0 >/dev/null 2>&1; then
  echo "FAIL: over-capacity bounded dynamic result unexpectedly succeeded" >&2
  exit 1
fi
for invalid_utf8 in \
  '1 128 0 0 0 0 0 0 0' \
  '2 192 128 0 0 0 0 0 0' \
  '3 237 160 128 0 0 0 0 0' \
  '2 226 130 0 0 0 0 0 0' \
  '4 244 144 128 128 0 0 0 0'; do
  # shellcheck disable=SC2086
  if "$cast" call --rpc-url "$rpc" "$addr" "$make_signature" $invalid_utf8 \
      >/dev/null 2>&1; then
    echo "FAIL: invalid UTF-8 bounded result unexpectedly succeeded ($invalid_utf8)" >&2
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

echo "evm-anvil-bounded: ok (canonical dynamic input/output + wide/constructed/tagged-in-array + UTF-8 matrix; engineering only)"
