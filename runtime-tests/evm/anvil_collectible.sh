#!/usr/bin/env bash
# Collectible: owner mint, approve, transferFrom over Erc721 ledger. Darwin + Linux.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

# Pack a 20-byte address into the ProofForge UInt256 limb layout (LE w0/w1/w2).
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

solana_lean_evm_init evm-anvil-collectible
bin="$root/build/evm/Collectible.bin"
if [[ ! -f "$bin" ]]; then
  echo "building Collectible.bin" >&2
  lake exe pf -- build --target evm --out "$root/build/evm" Collectible \
    || { echo "FAIL: pf build Collectible failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18570}" "$root/build/evm/anvil-collectible.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty Collectible.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
token_id=1
sender_packed="$(pf_pack_addr_u256 "$sender")"
other_packed="$(pf_pack_addr_u256 "$other")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  0 "absent minter balance"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  0 "absent token owner"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256)' "0x0000000000000000000000000000000000000000" "$token_id" \
    >/dev/null 2>&1; then
  echo "FAIL: mint to zero unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_zero_address "$addr" "$sender" \
  "$("$cast" calldata 'mint(address,uint256)' \
    '0x0000000000000000000000000000000000000000' "$token_id")" \
  "mint to zero"

if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'mint(address,uint256)' "$other" "$token_id" >/dev/null 2>&1; then
  echo "FAIL: non-owner mint unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'mint(address,uint256)' "$other" "$token_id")" "$other" \
  "non-owner mint"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'mint(address,uint256)' "$sender" "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  "$sender_packed" "owner after mint"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  1 "balance after mint"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'mint(address,uint256)' "$sender" "$token_id" >/dev/null 2>&1; then
  echo "FAIL: duplicate mint unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'mint(address,uint256)' "$sender" "$token_id")" "$sender" \
  "duplicate mint"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'approve(address,uint256)' "$other" "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'getApproved(uint256)(uint256)' "$token_id")" \
  "$other_packed" "approved spender"

"$cast" send --rpc-url "$rpc" --private-key "$other_key" \
  "$addr" 'transferFrom(address,address,uint256)' "$sender" "$other" "$token_id" >/dev/null
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'ownerOf(uint256)(uint256)' "$token_id")" \
  "$other_packed" "owner after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$sender")" \
  0 "sender balance after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'balanceOf(address)(uint256)' "$other")" \
  1 "recipient balance after transfer"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'getApproved(uint256)(uint256)' "$token_id")" \
  0 "approval cleared"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'transferFrom(address,address,uint256)' "$other" "$sender" "$token_id" \
    >/dev/null 2>&1; then
  echo "FAIL: unauthorized transfer unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$sender" \
  "$("$cast" calldata 'transferFrom(address,address,uint256)' "$other" "$sender" "$token_id")" \
  "$sender" "unauthorized transfer"

echo "evm-anvil-collectible: ok (mint/approve/transferFrom)"
