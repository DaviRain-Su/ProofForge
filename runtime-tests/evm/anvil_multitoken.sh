#!/usr/bin/env bash
# MultiToken: owner-minted bounded ERC-1155 core consumer. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-multitoken
bin="$root/build/evm/MultiToken.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered MultiToken.bin" >&2
  lake build Examples.MultiToken >/dev/null \
    || { echo "FAIL: lake build Examples.MultiToken failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" MultiToken >/dev/null \
    || { echo "FAIL: build registered MultiToken failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18574}" "$root/build/evm/anvil-multitoken.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty MultiToken.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
token_id=7
alias_id="$("$python" -I -S -c "print($token_id + (1 << 192))")"
zero="0x0000000000000000000000000000000000000000"

balance_of() { # owner id
  solana_lean_to_dec "$("$cast" call --rpc-url "$rpc" "$addr" \
    'balanceOf(address,uint256)(uint256)' "$1" "$2")"
}

solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 0 "absent balance"

# Zero recipient mint → ZeroAddress().
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256,uint256)' "$zero" "$token_id" 1 >/dev/null 2>&1; then
  echo "FAIL: mint to zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'mint(address,uint256,uint256)' "$zero" "$token_id" 1)" \
  "mint to zero"

# Non-minter mint → Unauthorized(other).
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'mint(address,uint256,uint256)' "$other" "$token_id" 1 >/dev/null 2>&1; then
  echo "FAIL: non-minter mint unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'mint(address,uint256,uint256)' "$other" "$token_id" 1)" "$other" \
  "non-minter mint"

# Unencodable id (id + 2^192) mint → Unauthorized; the view must not alias a live id.
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256,uint256)' "$sender" "$alias_id" 1 >/dev/null 2>&1; then
  echo "FAIL: mint on unencodable alias unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'mint(address,uint256,uint256)' "$sender" "$alias_id" 1)" "$sender" \
  "unencodable alias mint"
solana_lean_require_uint "$(balance_of "$sender" "$alias_id")" 0 "alias balance view gated"

# Owner mint 100 of id 7.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256,uint256)' "$sender" "$token_id" 100 >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 100 "balance after mint"
solana_lean_require_uint "$(balance_of "$sender" "$alias_id")" 0 \
  "alias does not see minted balance"

# Credit overflow: mint 2^256-10 of a fresh id, then +20 must wrap → Unauthorized, no write.
big_id=8
near_max="$("$python" -I -S -c "print((1 << 256) - 10)")"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256,uint256)' "$sender" "$big_id" "$near_max" >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$big_id")" "$near_max" "near-max balance"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256,uint256)' "$sender" "$big_id" 20 >/dev/null 2>&1; then
  echo "FAIL: wrapping credit unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$(balance_of "$sender" "$big_id")" "$near_max" \
  "overflow mint left balance untouched"

# Cross-owner movement: sender moves 40 to other.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transferFrom(address,address,uint256,uint256)' \
  "$sender" "$other" "$token_id" 40 >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 60 "source after transfer"
solana_lean_require_uint "$(balance_of "$other" "$token_id")" 40 "destination after transfer"

# Same-address transfer is a successful no-op after the debit gate.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'transferFrom(address,address,uint256,uint256)' \
  "$sender" "$sender" "$token_id" 15 >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 60 "self transfer keeps balance"

# Underflow: other owns 40, moving 41 as the owner passes auth but fails the debit gate.
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(address,address,uint256,uint256)' \
    "$other" "$sender" "$token_id" 41 >/dev/null 2>&1; then
  echo "FAIL: underflow transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$other" \
  "$("$cast" calldata 'transferFrom(address,address,uint256,uint256)' \
    "$other" "$sender" "$token_id" 41)" 40 41 "underflow transfer"
solana_lean_require_uint "$(balance_of "$other" "$token_id")" 40 "underflow left source untouched"
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 60 \
  "underflow left destination untouched"

# Unauthorized operator: other cannot move sender funds without approval.
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(address,address,uint256,uint256)' \
    "$sender" "$other" "$token_id" 1 >/dev/null 2>&1; then
  echo "FAIL: unauthorized operator transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'transferFrom(address,address,uint256,uint256)' \
    "$sender" "$other" "$token_id" 1)" "$other" "unauthorized operator transfer"
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 60 \
  "unauthorized transfer left source untouched"

# Approve operator, operator moves 5, revoke, operator is rejected again.
approved="$("$cast" call --rpc-url "$rpc" "$addr" \
  'isApprovedForAll(address,address)(bool)' "$sender" "$other")"
if [[ "${approved,,}" == "true" ]]; then
  echo "FAIL: operator unexpectedly approved" >&2
  exit 1
fi
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setApprovalForAll(address,bool)' "$other" true >/dev/null
approved="$("$cast" call --rpc-url "$rpc" "$addr" \
  'isApprovedForAll(address,address)(bool)' "$sender" "$other")"
if [[ "${approved,,}" != "true" ]]; then
  echo "FAIL: operator not approved (got $approved)" >&2
  exit 1
fi
"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'transferFrom(address,address,uint256,uint256)' \
  "$sender" "$other" "$token_id" 5 >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 55 "source after operator transfer"
solana_lean_require_uint "$(balance_of "$other" "$token_id")" 45 \
  "destination after operator transfer"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setApprovalForAll(address,bool)' "$other" false >/dev/null
approved="$("$cast" call --rpc-url "$rpc" "$addr" \
  'isApprovedForAll(address,address)(bool)' "$sender" "$other")"
if [[ "${approved,,}" == "true" ]]; then
  echo "FAIL: operator approval not revoked" >&2
  exit 1
fi
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'transferFrom(address,address,uint256,uint256)' \
    "$sender" "$other" "$token_id" 5 >/dev/null 2>&1; then
  echo "FAIL: revoked operator transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 55 "revoke left source untouched"
solana_lean_require_uint "$(balance_of "$other" "$token_id")" 45 "revoke left dest untouched"

# Burn: owner debits self; underflow and unencodable ids fail without writes.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'burn(uint256,uint256)' "$token_id" 5 >/dev/null
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 50 "balance after burn"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'burn(uint256,uint256)' "$token_id" 51 >/dev/null 2>&1; then
  echo "FAIL: underflow burn unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_insufficient "$addr" "$sender" \
  "$("$cast" calldata 'burn(uint256,uint256)' "$token_id" 51)" 50 51 "underflow burn"
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 50 "underflow burn untouched"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'burn(uint256,uint256)' "$alias_id" 1 >/dev/null 2>&1; then
  echo "FAIL: burn on unencodable alias unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'burn(uint256,uint256)' "$alias_id" 1)" "$sender" \
  "unencodable alias burn"

# Transfer to the zero address → ZeroAddress().
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'transferFrom(address,address,uint256,uint256)' \
    "$sender" "$zero" "$token_id" 1 >/dev/null 2>&1; then
  echo "FAIL: transfer to zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'transferFrom(address,address,uint256,uint256)' \
    "$sender" "$zero" "$token_id" 1)" "transfer to zero"
solana_lean_require_uint "$(balance_of "$sender" "$token_id")" 50 \
  "zero-address transfer left source untouched"

echo "evm-anvil-multitoken: ok (mint/burn/transferFrom/operator)"
