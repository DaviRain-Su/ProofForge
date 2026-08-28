#!/usr/bin/env bash
# Badge: operator approval + burn over Erc721 ledger. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

pf_pack_addr_u256() {
  local addr="$1"
  "$python" -I -S -c "
addr=int('$addr', 16)
b=addr.to_bytes(20, 'big')
w0=int.from_bytes(b[0:8], 'little')
w1=int.from_bytes(b[8:16], 'little')
w2=int.from_bytes(b[16:20], 'little')
print(w0 | (w1 << 64) | (w2 << 128))
"
}

solana_lean_evm_init evm-anvil-badge
bin="$root/build/evm/Badge.bin"
if [[ ! -f "$bin" ]]; then
  echo "building Badge.bin" >&2
  lake exe pf -- build --target evm --out "$root/build/evm" Badge \
    || { echo "FAIL: pf build Badge failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18571}" "$root/build/evm/anvil-badge.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Badge.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
token_id=42
sender_packed="$(pf_pack_addr_u256 "$sender")"
other_packed="$(pf_pack_addr_u256 "$other")"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256)' "$sender" "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  "$sender_packed" "owner after mint"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  1 "balance after mint"

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
  "$addr" 'transferFrom(address,address,uint256)' "$sender" "$other" "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  "$other_packed" "owner after operator transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$other")" \
  1 "operator recipient balance"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'burn(uint256)' "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  0 "owner cleared after burn"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$other")" \
  0 "balance after burn"

token_id2=43
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setApprovalForAll(address,bool)' "$other" false >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256)' "$sender" "$token_id2" >/dev/null
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'burn(uint256)' "$token_id2" >/dev/null 2>&1; then
  echo "FAIL: non-approved burn unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'burn(uint256)' "$token_id2")" "$other" \
  "non-approved burn"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id2")" \
  "$sender_packed" "non-approved burn holds owner"

# tokenKey drops w3; views/auth must not treat id+2^192 as the minted token.
alias_id="$("$python" -I -S -c "print($token_id2 + (1 << 192))")"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$alias_id")" \
  0 "ownerOf rejects unencodable alias"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'burn(uint256)' "$alias_id" >/dev/null 2>&1; then
  echo "FAIL: burn on unencodable alias unexpectedly succeeded" >&2
  exit 1
fi

echo "evm-anvil-badge: ok (operator transfer/burn)"
