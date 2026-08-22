#!/usr/bin/env bash
# Token: in-contract balances + allowance subtract + Transfer/Approval logs.
# Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-token
bin="$root/build/evm/Token.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18556}" "$root/build/evm/anvil-token.log"

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
[[ -n "$bytecode" ]] || { echo "FAIL: empty Token.bin" >&2; exit 1; }

addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
sender="$("$cast" wallet address --private-key "$private_key")"
sw="$(words_of "$sender")"
sw0="${sw%% *}"; srest="${sw#* }"; sw1="${srest%% *}"; sw2="${srest#* }"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
dest="$("$cast" wallet address --private-key "$other_key")"
dw="$(words_of "$dest")"
dw0="${dw%% *}"; drest="${dw#* }"; dw1="${drest%% *}"; dw2="${drest#* }"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  0 "absent sender balance"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(uint64,uint64,uint64,uint64)' "$sw0" "$sw1" "$sw2" 100 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  100 "minted sender"

topic_xfer="$("$cast" keccak 'Transfer(uint64)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transfer(uint64,uint64,uint64,uint64)' "$dw0" "$dw1" "$dw2" 30)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic_xfer'.lower()
ok=any((lg.get('topics') or [None])[0].lower()==want for lg in logs)
if not ok:
    raise SystemExit('FAIL: missing Transfer(uint64) log')
data=(logs[0].get('data') or '0x0')
if int(data,16)!=30:
    raise SystemExit(f'FAIL: transfer log data {data} != 30')
"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  70 "sender after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$dw0" "$dw1" "$dw2")" \
  30 "dest after transfer"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'transfer(uint64,uint64,uint64,uint64)' "$dw0" "$dw1" "$dw2" 1000 >/dev/null 2>&1; then
  echo "FAIL: overdraw transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  70 "overdraw holds sender"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$dw0" "$dw1" "$dw2")" \
  30 "overdraw holds dest"

topic_appr="$("$cast" keccak 'Approval(uint64)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'approve(uint64,uint64,uint64,uint64)' "$dw0" "$dw1" "$dw2" 20)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic_appr'.lower()
ok=any((lg.get('topics') or [None])[0].lower()==want for lg in logs)
if not ok:
    raise SystemExit('FAIL: missing Approval(uint64) log')
data=(logs[0].get('data') or '0x0')
if int(data,16)!=20:
    raise SystemExit(f'FAIL: approval log data {data} != 20')
"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$sw0" "$sw1" "$sw2" "$dw0" "$dw1" "$dw2")" \
  20 "allowance after approve"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'transferFrom(uint64,uint64,uint64,uint64,uint64,uint64,uint64)' \
  "$sw0" "$sw1" "$sw2" "$dw0" "$dw1" "$dw2" 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  65 "owner after transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$dw0" "$dw1" "$dw2")" \
  35 "dest after transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$sw0" "$sw1" "$sw2" "$dw0" "$dw1" "$dw2")" \
  15 "allowance after transferFrom"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(uint64,uint64,uint64,uint64,uint64,uint64,uint64)' \
    "$sw0" "$sw1" "$sw2" "$dw0" "$dw1" "$dw2" 100 >/dev/null 2>&1; then
  echo "FAIL: over-allowance transferFrom unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(uint64,uint64,uint64)(uint64)' "$sw0" "$sw1" "$sw2")" \
  65 "over-allowance holds owner"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(uint64,uint64,uint64,uint64,uint64,uint64)(uint64)' \
  "$sw0" "$sw1" "$sw2" "$dw0" "$dw1" "$dw2")" \
  15 "over-allowance holds remaining"

echo "evm-anvil-token: ok (mint/transfer/allowance; engineering only)"
