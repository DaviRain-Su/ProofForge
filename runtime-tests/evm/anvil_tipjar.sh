#!/usr/bin/env bash
# TipJar: env + payable deposit + sendEth + LOG1. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-tipjar
bin="$root/build/evm/TipJar.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18552}" "$root/build/evm/anvil-tipjar.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty TipJar.bin" >&2; exit 1; }

addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"
sender="$("$cast" wallet address --private-key "$private_key")"

solana_lean_require_uint "$("$cast" chain-id --rpc-url "$rpc")" "$chain_id" "anvil chain-id"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'chainId()(uint64)')" \
  "$chain_id" "evmChainId"

ts="$("$cast" block --rpc-url "$rpc" latest --json | "$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["timestamp"])')"
got_ts="$("$cast" call --rpc-url "$rpc" "$addr" 'timestamp()(uint64)')"
solana_lean_require_uint "$got_ts" "$(solana_lean_to_dec "$ts")" "evmTimestamp"

self_low="$("$python" -I -S -c "print(int('$addr', 16) & ((1<<64)-1))")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfLow()(uint64)')" \
  "$self_low" "evmSelf low-8"

words="$("$python" -I -S -c "
addr=int('$sender', 16)
b=addr.to_bytes(20, 'big')
def word(start, n):
    return int.from_bytes(b[start:start+n], 'little')
print(word(0,8), word(8,8), word(16,4))
")"
w0="${words%% *}"; rest="${words#* }"; w1="${rest%% *}"; w2="${rest#* }"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'callerW0()(uint64)')" \
  "$w0" "callerW0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'callerW1()(uint64)')" \
  "$w1" "callerW1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" --from "$sender" "$addr" 'callerW2()(uint64)')" \
  "$w2" "callerW2"

self_words="$("$python" -I -S -c "
addr=int('$addr', 16)
b=addr.to_bytes(20, 'big')
def word(start, n):
    return int.from_bytes(b[start:start+n], 'little')
print(word(0,8), word(8,8), word(16,4))
")"
sw0="${self_words%% *}"; srest="${self_words#* }"; sw1="${srest%% *}"; sw2="${srest#* }"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfW0()(uint64)')" \
  "$sw0" "selfW0"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfW1()(uint64)')" \
  "$sw1" "selfW1"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfW2()(uint64)')" \
  "$sw2" "selfW2"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'callValue()(uint256)')" \
  0 "view callValue is 0"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 1 \
    "$addr" 'logTip(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: nonpayable logTip unexpectedly accepted value" >&2
  exit 1
fi

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 3 \
    "$addr" 'deposit(uint256)' 7 >/dev/null 2>&1; then
  echo "FAIL: wrong-value deposit unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  0 "wrong deposit must not keep ETH"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 7 \
  "$addr" 'deposit(uint256)' 7 >/dev/null
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  7 "exact deposit must credit contract"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfBal()(uint256)')" \
  7 "evmSelfBalance after deposit"

recipient="$("$cast" wallet address --private-key 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)"
before="$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$recipient")")"
rw="$("$python" -I -S -c "
addr=int('$recipient', 16)
b=addr.to_bytes(20, 'big')
def word(start, n):
    return int.from_bytes(b[start:start+n], 'little')
print(word(0,8), word(8,8), word(16,4))
")"
rw0="${rw%% *}"; rrest="${rw#* }"; rw1="${rrest%% *}"; rw2="${rrest#* }"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'payout(address,uint256)' "$recipient" 3 >/dev/null
after="$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$recipient")")"
want="$("$python" -I -S -c "print(int('$before') + 3)")"
solana_lean_require_equal "$after" "$want" "payout must credit recipient"
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  4 "payout must debit contract"

topic="$("$cast" keccak 'Tipped(uint64)')"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'logTip(uint64)' 11)"
printf '%s' "$receipt" | "$python" -I -S -c "
import json,sys
r=json.load(sys.stdin)
logs=r.get('logs') or []
want='$topic'.lower()
ok=any((lg.get('topics') or [None])[0].lower()==want for lg in logs)
if not ok:
    raise SystemExit('FAIL: missing Tipped(uint64) log')
data=(logs[0].get('data') or '0x0')
if int(data, 16) != 11:
    raise SystemExit(f'FAIL: log data {data} != 11')
"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'notAFunction()' >/dev/null 2>&1; then
  echo "FAIL: unknown selector unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  4 "unknown selector must not keep ETH"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 1 \
    --data 0x1234 "$addr" >/dev/null 2>&1; then
  echo "FAIL: short calldata unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  4 "short calldata must not keep ETH"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 2 --data 0x "$addr" >/dev/null
solana_lean_require_equal "$(solana_lean_to_dec "$("$cast" balance --rpc-url "$rpc" "$addr")")" \
  6 "empty-calldata receive must credit contract"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'selfBal()(uint256)')" \
  6 "evmSelfBalance after receive"

echo "evm-anvil-tipjar: ok (env/deposit/payout/log/receive; engineering only)"
