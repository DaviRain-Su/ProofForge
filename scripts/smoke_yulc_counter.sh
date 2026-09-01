#!/usr/bin/env bash
# Smoke: compile Counter Yul with yulc (Feature B). Requires scripts/build_yulc.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

YULC="${PROOFFORGE_YULC:-$ROOT/powdr-probe/.lake/packages/yul_evm_compiler/.lake/build/bin/yulc}"
if [[ ! -x "$YULC" ]]; then
  echo "smoke_yulc_counter: yulc not found; run ./scripts/build_yulc.sh" >&2
  exit 1
fi

OUT="$ROOT/build/evm-yulc-smoke"
mkdir -p "$OUT"
lake exe pf -- build --target evm --out "$OUT" --backend solc Counter >/dev/null
[[ -f "$OUT/Counter.yul" ]] || { echo "smoke_yulc_counter: missing Counter.yul" >&2; exit 1; }

HEX="$("$YULC" --backend=classic "$OUT/Counter.yul" | tr -d '\n')"
if [[ -z "$HEX" ]]; then
  echo "smoke_yulc_counter: yulc returned empty bytecode" >&2
  exit 1
fi
echo "$HEX" >"$OUT/Counter.yulc.bin"

# Optional: pf yulc backend path
PROOFFORGE_YULC="$YULC" lake exe pf -- build --target evm --out "$OUT/yulc-pf" --backend yulc Counter >/dev/null
PF_HEX="$(tr -d '\n' <"$OUT/yulc-pf/Counter.bin")"
if [[ "$PF_HEX" != "$HEX" ]]; then
  echo "smoke_yulc_counter: pf --backend yulc bytecode differs from direct yulc" >&2
  exit 1
fi

echo "smoke_yulc_counter: ok (${#HEX} hex chars)"
