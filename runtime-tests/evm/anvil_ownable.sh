#!/usr/bin/env bash
# Ownable: owner slots + Incremented log + pair-key allowance. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ownable
bin="$root/build/evm/Ownable.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18555}" "$root/build/evm/anvil-ownable.log"

words_of() {
  "$python" -I -S -c "
addr=int('$1', 16)
b=addr.to_bytes(20, 'big')
def word(start, n):
    return int.from_bytes(b[start:start+n], 'little')
print(word(0,8), word(8,8), word(16,4))
"
}

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Ownable.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
ow="$(words_of "$sender")"
ow0="${ow%% *}"; orest="${ow#* }"; ow1="${orest%% *}"; ow2="${orest#* }"

addr="$(solana_lean_deploy_ctor_u64x3 "$bytecode" "$ow0" "$ow1" "$ow2")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerW0()(uint64)')" \
  "$ow0" "owner w0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerW1()(uint64)')" \
  "$ow1" "owner w1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'ownerW2()(uint64)')" \
  "$ow2" "owner w2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  0 "initial value"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'bump(uint64)' 3 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  3 "owner bump"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-owner bump unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  3 "non-owner bump holds"

topic="$("$cast" keccak 'Incremented(uint64)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'logInc(uint64)' 11)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic'.lower()
ok=any((lg.get('topics') or [None])[0].lower()==want for lg in logs)
if not ok:
    raise SystemExit('FAIL: missing Incremented(uint64) log')
data=(logs[0].get('data') or '0x0')
if int(data,16)!=11:
    raise SystemExit(f'FAIL: log data {data} != 11')
"

spender="$("$cast" wallet address --private-key "$other_key")"
sw="$(words_of "$spender")"
sw0="${sw%% *}"; srest="${sw#* }"; sw1="${srest%% *}"; sw2="${srest#* }"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$ow0" "$ow1" "$ow2" "$sw0" "$sw1" "$sw2")" \
  0 "absent allowance"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'approve(uint64,uint64,uint64,uint64,uint64,uint64,uint64)' \
  "$ow0" "$ow1" "$ow2" "$sw0" "$sw1" "$sw2" 20 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$ow0" "$ow1" "$ow2" "$sw0" "$sw1" "$sw2")" \
  20 "allowance after approve"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'spend(uint64,uint64,uint64,uint64,uint64,uint64,uint64)' \
  "$ow0" "$ow1" "$ow2" "$sw0" "$sw1" "$sw2" 7 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$ow0" "$ow1" "$ow2" "$sw0" "$sw1" "$sw2")" \
  7 "spend writes remaining as amt (closed overwrite, not ERC-20 subtract)"

echo "evm-anvil-ownable: ok (owner/log/allowance; engineering only)"
