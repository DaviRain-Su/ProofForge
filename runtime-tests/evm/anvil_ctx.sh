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

echo "evm-anvil-ctx: ok (caller/number + static aggregate ABI; engineering only)"
