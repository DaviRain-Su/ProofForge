#!/usr/bin/env bash
# Dual-backend Anvil gate: Flag u8 mask with solc vs yulc bytecode (E-B3).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"
# shellcheck source=runtime-tests/evm/lib_yulc.sh
source "$here/lib_yulc.sh"

solana_lean_evm_init evm-anvil-yulc-flag
solana_lean_yulc_or_skip evm-anvil-yulc-flag

out="$root/build/evm-yulc-anvil-flag"
solana_lean_dual_build_program Flag "$out"
solana_lean_dual_bytecode_note evm-anvil-yulc-flag

solana_lean_start_anvil "${PF_EVM_PORT:-18593}" "$root/build/evm/anvil-yulc-flag.log"

run_flag_suite() {
  local label="$1" bytecode="$2"
  local addr
  addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"

  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" \
    0 "$label: ctor getFlag"
  solana_lean_require_storage "$addr" 0 0 "$label: ctor flag slot"
  solana_lean_require_storage "$addr" 1 7 "$label: ctor count slot"

  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setFlag(uint64)' 1 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" \
    1 "$label: setFlag view"
  solana_lean_require_storage "$addr" 0 1 "$label: setFlag flag"
  solana_lean_require_storage "$addr" 1 7 "$label: setFlag keeps count"

  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" 'setFlag(uint64)' 256 >/dev/null 2>&1; then
    echo "FAIL: $label setFlag(256) should revert" >&2
    exit 1
  fi
  solana_lean_require_storage "$addr" 0 1 "$label: overflow holds flag"
  echo "$addr"
}

solc_addr="$(run_flag_suite solc "$SOLC_HEX")"
yulc_addr="$(run_flag_suite yulc "$YULC_HEX")"

solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'getFlag()(uint64)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'getFlag()(uint64)')" \
  "solc vs yulc final getFlag mismatch"

echo "evm-anvil-yulc-flag: ok (dual-backend behavior match; engineering only)"
