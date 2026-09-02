# Shared helpers for EVM Feature B (yulc) runtime gates.
# Source after runtime-tests/evm/lib.sh and solana_lean_evm_init.

solana_lean_yulc_or_skip() {
  local label="${1:-evm-yulc}"
  YULC="${PROOFFORGE_YULC:-$root/powdr-probe/.lake/packages/yul_evm_compiler/.lake/build/bin/yulc}"
  if [[ ! -x "$YULC" ]]; then
    echo "$label: skip: yulc not found (run ./scripts/build_yulc.sh)" >&2
    exit 0
  fi
  export YULC
}

# Build one program with solc and yulc; set SOLC_BIN and YULC_BIN.
solana_lean_dual_build_program() {
  local program="$1" out_base="$2"
  mkdir -p "$out_base"
  PROOFFORGE_YULC="$YULC" lake exe pf -- build --target evm --out "$out_base/solc" --backend solc "$program" >/dev/null
  PROOFFORGE_YULC="$YULC" lake exe pf -- build --target evm --out "$out_base/yulc" --backend yulc "$program" >/dev/null
  SOLC_BIN="$out_base/solc/${program}.bin"
  YULC_BIN="$out_base/yulc/${program}.bin"
  solana_lean_ensure_bin "$SOLC_BIN"
  solana_lean_ensure_bin "$YULC_BIN"
  SOLC_HEX="$(tr -d '\n\r ' <"$SOLC_BIN")"
  YULC_HEX="$(tr -d '\n\r ' <"$YULC_BIN")"
}

solana_lean_dual_bytecode_note() {
  local label="$1"
  if [[ "$SOLC_HEX" == "$YULC_HEX" ]]; then
    echo "$label: note: solc and yulc bytecode identical" >&2
  else
    echo "$label: note: bytecode differs (solc ${#SOLC_HEX} vs yulc ${#YULC_HEX} hex chars)" >&2
  fi
}
