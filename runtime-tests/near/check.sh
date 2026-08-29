#!/usr/bin/env bash
# NEAR engineering gate: emit every registered near program to WAT/wasm,
# then assert the wasm import table is env and required exports exist.
# Does NOT start near-sandbox / nearcore / testnet.
set -euo pipefail
cd "$(dirname "$0")/../.."

OUT=${OUT:-build/near}
lake exe pf -- build --target near --out "$OUT"

python3 - "$OUT" <<'PY'
import sys
from pathlib import Path

out = Path(sys.argv[1])
wats = sorted(out.glob("*.wat"))
wasms = sorted(out.glob("*.wasm"))
if not wats:
    sys.exit("near check: no .wat produced")
if len(wats) != len(wasms):
    sys.exit(f"near check: wat/wasm count mismatch {len(wats)}/{len(wasms)}")

need_imports = (
    '(import "env" "input"',
    '(import "env" "storage_read"',
    '(import "env" "storage_write"',
    '(import "env" "value_return"',
)
need_exports = (
    '(func (export "initialize")',
    '(func (export "increment")',
    '(func (export "get")',
)
forbid = ("host_lib", "xrpl_wasm_std", "get_current_contract_call")

for wat in wats:
    text = wat.read_text(encoding="utf-8")
    for needle in need_imports + need_exports:
        if needle not in text:
            sys.exit(f"near check: {wat.name} missing {needle!r}")
    for needle in forbid:
        if needle in text:
            sys.exit(f"near check: {wat.name} still contains {needle!r}")
    wasm = out / f"{wat.stem}.wasm"
    if not wasm.is_file() or wasm.stat().st_size == 0:
        sys.exit(f"near check: missing wasm {wasm.name}")
    magic = wasm.read_bytes()[:4]
    if magic != b"\x00asm":
        sys.exit(f"near check: {wasm.name} is not wasm")
    print(f"near check ok: {wat.name} / {wasm.name}")
print("near engineering gate: ok")
PY
