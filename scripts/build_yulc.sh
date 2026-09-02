#!/usr/bin/env bash
# Build powdr-labs yulc from the isolated powdr-probe package (EVM Feature B).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PKG="$ROOT/powdr-probe/.lake/packages/yul_evm_compiler"
if [[ ! -d "$PKG" ]]; then
  echo "build_yulc: run ./scripts/build_powdr_probe.sh first to fetch yul-compiler" >&2
  exit 1
fi
cd "$PKG"
if command -v lake >/dev/null 2>&1; then
  lake exe cache get 2>/dev/null || true
fi
lake build yulc
BIN="$PKG/.lake/build/bin/yulc"
if [[ ! -x "$BIN" ]]; then
  echo "build_yulc: expected binary at $BIN" >&2
  exit 1
fi
echo "build_yulc: ok ($BIN)"
