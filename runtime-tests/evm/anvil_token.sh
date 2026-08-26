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
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  0 "absent total supply"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'decimals()(uint8)')" \
  18 "compile-time decimals"

zero="0x0000000000000000000000000000000000000000"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256)' "$zero" 1 >/dev/null 2>&1; then
  echo "FAIL: mint to zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'mint(address,uint256)' "$zero" 1)" \
  "mint to zero"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  0 "mint to zero holds supply"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256)' "$sender" 100 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  100 "minted sender"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  100 "total supply after mint"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'decimals()(uint8)')" \
  18 "decimals holds after mint"

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
  'totalSupply()(uint256)')" \
  100 "total supply holds after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$dest")" \
  30 "dest after transfer"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'transfer(address,uint256)' "$zero" 1 >/dev/null 2>&1; then
  echo "FAIL: transfer to zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'transfer(address,uint256)' "$zero" 1)" \
  "transfer to zero"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  70 "transfer to zero holds sender"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'approve(address,uint256)' "$zero" 1 >/dev/null 2>&1; then
  echo "FAIL: approve zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'approve(address,uint256)' "$zero" 1)" \
  "approve zero"

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

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'increaseAllowance(address,uint256)' "$dest" 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  25 "allowance after increase"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'decreaseAllowance(address,uint256)' "$dest" 10 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  15 "allowance after decrease"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'decreaseAllowance(address,uint256)' "$dest" 100 >/dev/null 2>&1; then
  echo "FAIL: over-decrease unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$sender" \
  "$("$cast" calldata 'decreaseAllowance(address,uint256)' "$dest" 100)" \
  15 100 "over-decrease allowance"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  15 "over-decrease holds remaining"

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
  10 "allowance after transferFrom"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(address,address,uint256)' "$sender" "$dest" 100 >/dev/null 2>&1; then
  echo "FAIL: over-allowance transferFrom unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$dest" \
  "$("$cast" calldata 'transferFrom(address,address,uint256)' "$sender" "$dest" 100)" \
  10 100 "over-allowance transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  65 "over-allowance holds owner"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  10 "over-allowance holds remaining"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'burnFrom(address,uint256)' "$sender" 5 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  60 "owner after burnFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  5 "allowance after burnFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  95 "total supply after burnFrom"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'burnFrom(address,uint256)' "$sender" 100 >/dev/null 2>&1; then
  echo "FAIL: over-allowance burnFrom unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$dest" \
  "$("$cast" calldata 'burnFrom(address,uint256)' "$sender" 100)" \
  5 100 "over-allowance burnFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  60 "over-allowance burnFrom holds owner"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  5 "over-allowance burnFrom holds remaining"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  95 "over-allowance burnFrom holds supply"

deadline=9999999999
typed="$(printf '%s' "{
  \"types\": {
    \"EIP712Domain\": [
      {\"name\":\"name\",\"type\":\"string\"},
      {\"name\":\"version\",\"type\":\"string\"},
      {\"name\":\"chainId\",\"type\":\"uint256\"},
      {\"name\":\"verifyingContract\",\"type\":\"address\"}
    ],
    \"Permit\": [
      {\"name\":\"owner\",\"type\":\"address\"},
      {\"name\":\"spender\",\"type\":\"address\"},
      {\"name\":\"value\",\"type\":\"uint256\"},
      {\"name\":\"nonce\",\"type\":\"uint256\"},
      {\"name\":\"deadline\",\"type\":\"uint256\"}
    ]
  },
  \"primaryType\": \"Permit\",
  \"domain\": {
    \"name\": \"Token\",
    \"version\": \"1\",
    \"chainId\": $chain_id,
    \"verifyingContract\": \"$addr\"
  },
  \"message\": {
    \"owner\": \"$sender\",
    \"spender\": \"$dest\",
    \"value\": \"10\",
    \"nonce\": \"0\",
    \"deadline\": \"$deadline\"
  }
}")"
sig="$("$cast" wallet sign --data --private-key "$private_key" "$typed")"
r="0x${sig:2:64}"
s="0x${sig:66:64}"
v="$((16#${sig:130:2}))"

wrong_sig="$("$cast" wallet sign --data --private-key "$other_key" "$typed")"
wrong_r="0x${wrong_sig:2:64}"
wrong_s="0x${wrong_sig:66:64}"
wrong_v="$((16#${wrong_sig:130:2}))"
wrong_data="$("$cast" calldata 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)' \
  "$sender" "$dest" 10 "$deadline" "$wrong_v" "$wrong_r" "$wrong_s")"
solana_lean_require_unauthorized "$addr" "$dest" "$wrong_data" "$dest" \
  "permit signed by spender"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)' \
  "$sender" "$dest" 10 "$deadline" "$v" "$r" "$s" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  10 "allowance after permit"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'nonceOf(address)(uint256)' "$sender")" \
  1 "nonce after permit"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'transferFrom(address,address,uint256)' "$sender" "$dest" 10 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  50 "owner after permit transferFrom"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowanceOf(address,address)(uint256)' "$sender" "$dest")" \
  0 "allowance after permit transferFrom"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'burn(uint256)' 10 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  40 "owner after burn"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  85 "total supply after burn"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'burn(uint256)' 1000 >/dev/null 2>&1; then
  echo "FAIL: overdraw burn unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$sender" \
  "$("$cast" calldata 'burn(uint256)' 1000)" \
  40 1000 "overdraw burn"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  40 "overdraw burn holds owner"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'totalSupply()(uint256)')" \
  85 "overdraw burn holds supply"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)' \
    "$sender" "$dest" 10 0 "$v" "$r" "$s" >/dev/null 2>&1; then
  echo "FAIL: expired permit unexpectedly succeeded" >&2
  exit 1
fi

got_dom="$("$cast" call --rpc-url "$rpc" "$addr" 'DOMAIN_SEPARATOR()(bytes32)')"
if [[ ! "$got_dom" =~ ^0x[0-9a-fA-F]{64}$ ]]; then
  echo "FAIL: DOMAIN_SEPARATOR not bytes32: $got_dom" >&2
  exit 1
fi
got_dom2="$("$cast" call --rpc-url "$rpc" "$addr" 'DOMAIN_SEPARATOR()(bytes32)')"
solana_lean_require_equal "${got_dom2,,}" "${got_dom,,}" "DOMAIN_SEPARATOR holds after permit"

echo "evm-anvil-token: ok (mint/transfer/allowance/LOG3/Insufficient/permit/domain/burn/burnFrom/incdec/decimals/zero; engineering only)"
