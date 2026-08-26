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

echo "evm-anvil-vault: ok (map/share/token/approve/transferFrom; engineering only)"
