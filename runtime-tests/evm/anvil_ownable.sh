#!/usr/bin/env bash
# Ownable: owner Addr20 + Incremented log + pair-key allowance. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-ownable
bin="$root/build/evm/Ownable.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18555}" "$root/build/evm/anvil-ownable.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Ownable.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"
got_owner="$("$cast" call --rpc-url "$rpc" "$addr" 'ownerOf()(address)')"
solana_lean_require_equal "${got_owner,,}" "${sender,,}" "ownerOf"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  0 "initial value"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'bump(uint64)' 3 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  3 "owner bump"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
bump_data="$("$cast" calldata 'bump(uint64)' 1)"
solana_lean_require_unauthorized "$addr" "$other" "$bump_data" "$other" "non-owner bump"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'bump(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-owner bump unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
  3 "non-owner bump holds"

zero="0x0000000000000000000000000000000000000000"
zero_data="$("$cast" calldata 'guardZero(address)' "$zero")"
solana_lean_require_zero_address "$addr" "$sender" "$zero_data" "zero address"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'guardZero(address)(uint64)' "$sender")" \
  "$("$python" -I -S -c "print(int.from_bytes(bytes.fromhex('${sender#0x}'[:16]), 'little'))")" \
  "guardZero non-zero returns Addr20.w0"

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
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(address,address)(uint64)' "$sender" "$spender")" \
  0 "absent allowance"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'approve(address,address,uint64)' "$sender" "$spender" 20 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(address,address)(uint64)' "$sender" "$spender")" \
  20 "allowance after approve"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'spend(address,address,uint64)' "$sender" "$spender" 7 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowance(address,address)(uint64)' "$sender" "$spender")" \
  7 "spend writes remaining as amt (closed overwrite, not ERC-20 subtract)"

echo "evm-anvil-ownable: ok (owner/log/allowance; engineering only)"
