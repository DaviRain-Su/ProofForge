#!/usr/bin/env bash
# Vault: hashed Map + closed ERC-20. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-vault
bin="$root/build/evm/Vault.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18554}" "$root/build/evm/anvil-vault.log"

solc_bin=""
for c in /opt/homebrew/bin/solc /usr/local/bin/solc solc; do
  if command -v "$c" >/dev/null 2>&1 || [[ -x "$c" ]]; then
    solc_bin="$c"
    break
  fi
done
if [[ -z "$solc_bin" ]]; then
  echo "evm-anvil-vault: skip: solc not found" >&2
  exit 0
fi

mock_out="$root/build/evm/ERC20Mock.bin"
"$solc_bin" --bin --optimize --overwrite -o "$root/build/evm" \
  "$here/ERC20Mock.sol" >/dev/null
[[ -f "$mock_out" ]] || { echo "FAIL: missing ERC20Mock.bin" >&2; exit 1; }

bytecode="$(tr -d '\n\r ' < "$bin")"
addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 0)"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getU64(uint64)(uint64)' 7)" \
  0 "absent map u64"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setU64(uint64,uint64)' 7 9 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getU64(uint64)(uint64)' 7)" \
  9 "map u64 after set"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getU64(uint64)(uint64)' 8)" \
  0 "other key stays absent"

sender="$("$cast" wallet address --private-key "$private_key")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shareOf(address)(uint256)' "$sender")" \
  0 "absent share"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'credit(address,uint256)' "$sender" 11 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shareOf(address)(uint256)' "$sender")" \
  11 "share after credit"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'credit(address,uint256)' "$sender" 4 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shareOf(address)(uint256)' "$sender")" \
  15 "share after additive credit"
max_uint="0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'credit(address,uint256)' "$sender" "$max_uint" >/dev/null 2>&1; then
  echo "FAIL: overflowing share credit unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'shareOf(address)(uint256)' "$sender")" \
  15 "overflowing credit holds share"

mock_hex="$(tr -d '\n\r ' < "$mock_out")"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" --create "0x$mock_hex")"
token="$(printf '%s' "$receipt" | solana_lean_contract_address)"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'mint(address,uint256)' "$addr" 1000 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  1000 "balanceOfSelf after mint"

recipient="$("$cast" wallet address --private-key 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'pull(address,address,uint256)' "$token" "$recipient" 100 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  900 "balanceOfSelf after pull"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$token" 'balanceOf(address)(uint256)' "$recipient")" \
  100 "recipient token after pull"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pull(address,address,uint256)' "$recipient" "$recipient" 1 >/dev/null 2>&1; then
  echo "FAIL: no-code token target unexpectedly accepted empty returndata" >&2
  exit 1
fi

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pull(address,address,uint256)' "$token" "$recipient" 10000 >/dev/null 2>&1; then
  echo "FAIL: overdraw pull unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  900 "overdraw holds vault token"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setNoReturn(bool)' true >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'pull(address,address,uint256)' "$token" "$recipient" 50 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  850 "USDT-style no-return transfer succeeds"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setNoReturn(bool)' false >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setReturnFalse(bool)' true >/dev/null
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pull(address,address,uint256)' "$token" "$recipient" 10 >/dev/null 2>&1; then
  echo "FAIL: false-returning token transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  850 "false-returning transfer rolls back token state"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setReturnFalse(bool)' false >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setReturnTwo(bool)' true >/dev/null
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'pull(address,address,uint256)' "$token" "$recipient" 10 >/dev/null 2>&1; then
  echo "FAIL: noncanonical bool word 2 unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  850 "noncanonical bool transfer rolls back token state"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setReturnTwo(bool)' false >/dev/null

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowed(address,address,address)(uint256)' "$token" "$addr" "$recipient")" \
  0 "absent allowance"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grant(address,address,uint256)' "$token" "$recipient" 40 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$token" \
  'allowance(address,address)(uint256)' "$addr" "$recipient")" \
  40 "token allowance after grant"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'allowed(address,address,address)(uint256)' "$token" "$addr" "$recipient")" \
  40 "vault allowed after grant"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'mint(address,uint256)' "$sender" 200 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'approve(address,uint256)' "$addr" 80 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'take(address,address,address,uint256)' "$token" "$sender" "$recipient" 25 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$token" \
  'balanceOf(address)(uint256)' "$sender")" \
  175 "owner after vault take"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$token" \
  'balanceOf(address)(uint256)' "$recipient")" \
  175 "recipient after vault take"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$token" \
  'allowance(address,address)(uint256)' "$sender" "$addr")" \
  55 "remaining allowance after take"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'take(address,address,address,uint256)' "$token" "$sender" "$recipient" 1000 >/dev/null 2>&1; then
  echo "FAIL: over-allowance take unexpectedly succeeded" >&2
  exit 1
fi

weth_out="$root/build/evm/WETHMock.bin"
"$solc_bin" --bin --optimize --overwrite -o "$root/build/evm" \
  "$here/WETHMock.sol" >/dev/null
[[ -f "$weth_out" ]] || { echo "FAIL: missing WETHMock.bin" >&2; exit 1; }
weth_hex="$(tr -d '\n\r ' < "$weth_out")"
weth_receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" --create "0x$weth_hex")"
weth="$(printf '%s' "$weth_receipt" | solana_lean_contract_address)"

before_eth="$("$cast" balance --rpc-url "$rpc" "$addr")"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 40 \
  "$addr" 'wrap(address,uint256)' "$weth" 40 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$weth")" \
  40 "held WETH after wrap"
after_wrap_eth="$("$cast" balance --rpc-url "$rpc" "$addr")"
solana_lean_require_uint "$after_wrap_eth" "$(solana_lean_to_dec "$before_eth")" \
  "wrap must send ETH into WETH, not keep it"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'unwrap(address,uint256)' "$weth" 15 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$weth")" \
  25 "held WETH after unwrap"
after_unwrap_eth="$("$cast" balance --rpc-url "$rpc" "$addr")"
solana_lean_require_uint "$after_unwrap_eth" \
  "$("$python" -I -S -c "print(int('$(solana_lean_to_dec "$before_eth")') + 15)")" \
  "unwrap must credit ETH back to vault"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 7 \
    "$addr" 'wrap(address,uint256)' "$weth" 40 >/dev/null 2>&1; then
  echo "FAIL: wrong-value wrap unexpectedly succeeded" >&2
  exit 1
fi

router_out="$root/build/evm/RouterMock.bin"
"$solc_bin" --bin --optimize --overwrite -o "$root/build/evm" \
  "$here/RouterMock.sol" >/dev/null
[[ -f "$router_out" ]] || { echo "FAIL: missing RouterMock.bin" >&2; exit 1; }
router_hex="$(tr -d '\n\r ' < "$router_out")"
router_receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" --create "0x$router_hex")"
router="$(printf '%s' "$router_receipt" | solana_lean_contract_address)"

token_b_receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" --create "0x$mock_hex")"
token_b="$(printf '%s' "$token_b_receipt" | solana_lean_contract_address)"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'setNoReturn(bool)' false >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$token" 'mint(address,uint256)' "$addr" 50 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'grant(address,address,uint256)' "$token" "$router" 50 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'swap2(address,address,address,uint256,uint256)' \
  "$router" "$token" "$token_b" 30 1 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  870 "token A after swap2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token_b")" \
  30 "token B after swap2"

token_c_receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" --create "0x$mock_hex")"
token_c="$(printf '%s' "$token_c_receipt" | solana_lean_contract_address)"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'swap3(address,address,address,address,uint256,uint256)' \
  "$router" "$token" "$token_b" "$token_c" 20 1 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token")" \
  850 "token A after swap3"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'held(address)(uint256)' "$token_c")" \
  20 "token C after swap3"

internal_bin="$root/build/evm/Token.bin"
solana_lean_ensure_bin "$internal_bin"
internal_hex="$(tr -d '\n\r ' < "$internal_bin")"
internal="$(solana_lean_deploy_ctor_address "$internal_hex" "$sender")"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$internal" 'mint(address,uint256)' "$sender" 80 >/dev/null
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
    \"verifyingContract\": \"$internal\"
  },
  \"message\": {
    \"owner\": \"$sender\",
    \"spender\": \"$addr\",
    \"value\": \"12\",
    \"nonce\": \"0\",
    \"deadline\": \"$deadline\"
  }
}")"
sig="$("$cast" wallet sign --data --private-key "$private_key" "$typed")"
r="0x${sig:2:64}"
s="0x${sig:66:64}"
v="$((16#${sig:130:2}))"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'permit(address,address,address,uint256,uint256,uint8,bytes32,bytes32)' \
  "$internal" "$sender" "$addr" 12 "$deadline" "$v" "$r" "$s" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$internal" \
  'allowanceOf(address,address)(uint256)' "$sender" "$addr")" \
  12 "internal token allowance after vault permit"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'take(address,address,address,uint256)' \
  "$internal" "$sender" "$recipient" 12 >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$internal" \
  'balanceOf(address)(uint256)' "$sender")" \
  68 "owner after vault permit take"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$internal" \
  'allowanceOf(address,address)(uint256)' "$sender" "$addr")" \
  0 "allowance after vault permit take"

echo "evm-anvil-vault: ok (map/share/token/approve/transferFrom/weth/swap2/swap3/permit; engineering only)"
