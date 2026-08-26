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

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Token.bin" >&2; exit 1; }

addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
sender="$("$cast" wallet address --private-key "$private_key")"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
dest="$("$cast" wallet address --private-key "$other_key")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  0 "absent sender balance"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256)' "$sender" 100 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  100 "minted sender"

topic_xfer="$("$cast" keccak 'Transfer(address,address,uint256)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transfer(address,uint256)' "$dest" 30)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic_xfer'.lower()
sender=int('$sender', 16)
dest=int('$dest', 16)
hit=None
for lg in logs:
    topics=lg.get('topics') or []
    if topics and topics[0].lower()==want:
        hit=lg
        break
if hit is None:
    raise SystemExit('FAIL: missing Transfer(address,address,uint256) log')
topics=hit.get('topics') or []
if len(topics)!=3:
    raise SystemExit(f'FAIL: Transfer should be LOG3, got {len(topics)} topics')
if int(topics[1],16)!=sender:
    raise SystemExit(f'FAIL: Transfer from {topics[1]} != sender')
if int(topics[2],16)!=dest:
    raise SystemExit(f'FAIL: Transfer to {topics[2]} != dest')
data=int(hit.get('data') or '0x0', 16)
if data!=30:
    raise SystemExit(f'FAIL: transfer log data {data} != 30')
"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  70 "sender after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$dest")" \
  30 "dest after transfer"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'transfer(address,uint256)' "$dest" 1000 >/dev/null 2>&1; then
  echo "FAIL: overdraw transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$sender" \
  "$("$cast" calldata 'transfer(address,uint256)' "$dest" 1000)" \
  70 1000 "overdraw transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  70 "overdraw holds sender"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$dest")" \
  30 "overdraw holds dest"

topic_appr="$("$cast" keccak 'Approval(address,address,uint256)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'approve(address,uint256)' "$dest" 20)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic_appr'.lower()
sender=int('$sender', 16)
dest=int('$dest', 16)
hit=None
for lg in logs:
    topics=lg.get('topics') or []
    if topics and topics[0].lower()==want:
        hit=lg
        break
if hit is None:
    raise SystemExit('FAIL: missing Approval(address,address,uint256) log')
topics=hit.get('topics') or []
if len(topics)!=3:
    raise SystemExit(f'FAIL: Approval should be LOG3, got {len(topics)} topics')
if int(topics[1],16)!=sender:
    raise SystemExit(f'FAIL: Approval owner {topics[1]} != sender')
if int(topics[2],16)!=dest:
    raise SystemExit(f'FAIL: Approval spender {topics[2]} != dest')
data=int(hit.get('data') or '0x0', 16)
if data!=20:
    raise SystemExit(f'FAIL: approval log data {data} != 20')
"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  20 "allowance after approve"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'transferFrom(address,address,uint256)' "$sender" "$dest" 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  65 "owner after transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$dest")" \
  35 "dest after transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  15 "allowance after transferFrom"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(address,address,uint256)' "$sender" "$dest" 100 >/dev/null 2>&1; then
  echo "FAIL: over-allowance transferFrom unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$dest" \
  "$("$cast" calldata 'transferFrom(address,address,uint256)' "$sender" "$dest" 100)" \
  15 100 "over-allowance transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  65 "over-allowance holds owner"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  15 "over-allowance holds remaining"

echo "evm-anvil-token: ok (mint/transfer/allowance/LOG3/Insufficient; engineering only)"
