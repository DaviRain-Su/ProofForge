#!/usr/bin/env bash
# Dual-backend Anvil gate: Counter behavior with solc vs yulc bytecode (E-B3 seed).
# Missing anvil/cast/yulc → skip (exit 0). Bytecode may differ; storage behavior must match.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-yulc-counter

yulc="${PROOFFORGE_YULC:-$root/powdr-probe/.lake/packages/yul_evm_compiler/.lake/build/bin/yulc}"
if [[ ! -x "$yulc" ]]; then
  echo "evm-anvil-yulc-counter: skip: yulc not found (run ./scripts/build_yulc.sh)" >&2
  exit 0
fi

out="$root/build/evm-yulc-anvil"
mkdir -p "$out"
PROOFFORGE_YULC="$yulc" lake exe pf -- build --target evm --out "$out/solc" --backend solc Counter >/dev/null
PROOFFORGE_YULC="$yulc" lake exe pf -- build --target evm --out "$out/yulc" --backend yulc Counter >/dev/null

solc_bin="$out/solc/Counter.bin"
yulc_bin="$out/yulc/Counter.bin"
solana_lean_ensure_bin "$solc_bin"
solana_lean_ensure_bin "$yulc_bin"

solc_hex="$(tr -d '\n\r ' <"$solc_bin")"
yulc_hex="$(tr -d '\n\r ' <"$yulc_bin")"
if [[ "$solc_hex" == "$yulc_hex" ]]; then
  echo "evm-anvil-yulc-counter: note: solc and yulc bytecode identical for Counter" >&2
else
  echo "evm-anvil-yulc-counter: note: bytecode differs (solc ${#solc_hex} vs yulc ${#yulc_hex} hex chars)" >&2
fi

solana_lean_start_anvil "${PF_EVM_PORT:-18590}" "$root/build/evm/anvil-yulc-counter.log"

run_counter_suite() {
  local label="$1" bytecode="$2"
  local addr
  addr="$(solana_lean_deploy_ctor_u64 "$bytecode" 7)"
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    7 "$label: constructor view"
  solana_lean_require_storage "$addr" 0 7 "$label: constructor storage"
  "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'increment(uint64)' 5 >/dev/null
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" \
    12 "$label: post-increment view"
  solana_lean_require_storage "$addr" 0 12 "$label: post-increment storage"
  echo "$addr"
}

solc_addr="$(run_counter_suite solc "$solc_hex")"
yulc_addr="$(run_counter_suite yulc "$yulc_hex")"

# Cross-check both contracts reached the same logical state.
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$solc_addr" 'get()(uint64)')" \
  "$("$cast" call --rpc-url "$rpc" "$yulc_addr" 'get()(uint64)')" \
  "solc vs yulc final get() mismatch"

echo "evm-anvil-yulc-counter: ok (dual-backend behavior match; engineering only)"
