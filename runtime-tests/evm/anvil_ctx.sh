#!/usr/bin/env bash
# EvmCtx: evmCaller / evmBlockNumber. Not clockSlot / signerKey0.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ctx
bin="$root/build/evm/EvmCtx.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18551}" "$root/build/evm/anvil-ctx.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

sender="$("$cast" wallet address --private-key "$private_key")"
want_caller="$("$python" -I -S -c "print(int('$sender', 16) & ((1<<64)-1))")"
got_caller="$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'caller()(uint64)')"
solana_lean_require_uint "$got_caller" "$want_caller" "caller low-8"

bn="$("$cast" block-number --rpc-url "$rpc")"
got_h="$("$cast" call --rpc-url "$rpc" "$addr" 'height()(uint64)')"
solana_lean_require_uint "$got_h" "$(solana_lean_to_dec "$bn")" "height == block number"

gas_left="$(solana_lean_to_dec "$("$cast" call --rpc-url "$rpc" "$addr" 'gasLeft()(uint256)')")"
if [[ "$gas_left" -le 0 ]]; then
  echo "FAIL: gasLeft must expose a positive full-width GAS observation, got $gas_left" >&2
  exit 1
fi

previous="$(( $(solana_lean_to_dec "$bn") - 1 ))"
previous_hash="$("$cast" block --rpc-url "$rpc" "$previous" --json |
  "$python" -I -S -c 'import json,sys; print(int(json.load(sys.stdin)["hash"], 16))')"
solana_lean_require_uint \
  "$("$cast" call --rpc-url "$rpc" "$addr" 'blockHash(uint64)(uint256)' "$previous")" \
  "$previous_hash" "BLOCKHASH previous block"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'stamp()' >/dev/null
got_get="$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')"
bn2="$("$cast" block-number --rpc-url "$rpc")"
# stamp mined in some block; stored value must be that block or the one just before get.
stored="$(solana_lean_to_dec "$got_get")"
now="$(solana_lean_to_dec "$bn2")"
if [[ "$stored" != "$now" && "$stored" != "$((now - 1))" ]]; then
  echo "FAIL: stamp stored $stored, block now $now" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 0 "$stored" "stamp wrote dummy"

aggregate="$("$cast" call --rpc-url "$rpc" "$addr" \
  'aggregate((uint64,(uint8,bool)),(uint32,uint64),uint16[3])((uint64,bool))' \
  '(11,(3,true))' '(13,17)' '[19,23,29]')"
aggregate_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$aggregate''')))" )"
solana_lean_require_equal "$aggregate_values" "93 true" "static aggregate ABI"

aggregate_selector="$("$cast" sig 'aggregate((uint64,(uint8,bool)),(uint32,uint64),uint16[3])')"
bad_bool="${aggregate_selector}$("$python" -I -S -c \
  "print(''.join(f'{v:064x}' for v in [11, 3, 2, 13, 17, 19, 23, 29]))")"
if "$cast" call --rpc-url "$rpc" "$addr" --data "$bad_bool" >/dev/null 2>&1; then
  echo "FAIL: aggregate noncanonical bool unexpectedly succeeded" >&2
  exit 1
fi

option_none="$("$cast" call --rpc-url "$rpc" "$addr" \
  'optionValue((bool,uint64))(uint64)' '(false,0)')"
solana_lean_require_uint "$option_none" 5 "Tagged Tuple v1 Option.none"
option_some="$("$cast" call --rpc-url "$rpc" "$addr" \
  'optionValue((bool,uint64))(uint64)' '(true,37)')"
solana_lean_require_uint "$option_some" 38 "Tagged Tuple v1 Option.some"

tagged_idle="$("$cast" call --rpc-url "$rpc" "$addr" \
  'taggedValue((uint8,uint64,uint64))(uint64)' '(0,0,0)')"
solana_lean_require_uint "$tagged_idle" 3 "Tagged Tuple v1 idle"
tagged_one="$("$cast" call --rpc-url "$rpc" "$addr" \
  'taggedValue((uint8,uint64,uint64))(uint64)' '(1,7,0)')"
solana_lean_require_uint "$tagged_one" 17 "Tagged Tuple v1 one"
tagged_pair="$("$cast" call --rpc-url "$rpc" "$addr" \
  'taggedValue((uint8,uint64,uint64))(uint64)' '(2,11,29)')"
solana_lean_require_uint "$tagged_pair" 40 "Tagged Tuple v1 pair"

option_selector="$("$cast" sig 'optionValue((bool,uint64))')"
tagged_selector="$("$cast" sig 'taggedValue((uint8,uint64,uint64))')"
echo_option_selector="$("$cast" sig 'echoOptionValue((bool,uint64))')"
echo_tagged_selector="$("$cast" sig 'echoTaggedValue((uint8,uint64,uint64))')"
word_data() {
  local selector="$1"
  shift
  "$python" -I -S -c \
    "import sys; print(sys.argv[1] + ''.join(f'{int(v):064x}' for v in sys.argv[2:]))" \
    "$selector" "$@"
}

return_words() {
  "$python" -I -S -c \
    "import sys; print('0x' + ''.join(f'{int(v):064x}' for v in sys.argv[1:]))" "$@"
}

# Output plans rebuild the same public fixed tuple from an independent source frame and re-run
# tag/inactive-lane checks before publishing returndata.
for case in \
  "$echo_option_selector|0 0" \
  "$echo_option_selector|1 37" \
  "$echo_tagged_selector|0 0 0" \
  "$echo_tagged_selector|1 7 0" \
  "$echo_tagged_selector|2 11 29"; do
  selector="${case%%|*}"
  words="${case#*|}"
  # shellcheck disable=SC2086
  echoed="$("$cast" call --rpc-url "$rpc" "$addr" --data "$(word_data "$selector" $words)")"
  # shellcheck disable=SC2086
  expected="$(return_words $words)"
  solana_lean_require_equal "$echoed" "$expected" "Tagged Tuple v1 result $words"
done

for malformed in \
  "$(word_data "$option_selector" 0 1)" \
  "$(word_data "$option_selector" 2 0)" \
  "$(word_data "$tagged_selector" 3 0 0)" \
  "$(word_data "$tagged_selector" 0 1 0)" \
  "$(word_data "$tagged_selector" 1 7 1)"; do
  if "$cast" call --rpc-url "$rpc" "$addr" --data "$malformed" >/dev/null 2>&1; then
    echo "FAIL: noncanonical Tagged Tuple v1 calldata unexpectedly succeeded" >&2
    exit 1
  fi
done

echo "evm-anvil-ctx: ok (caller/number/gas/blockhash + static/tagged aggregate ABI; engineering only)"
