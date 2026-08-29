#!/usr/bin/env bash
# XRPL Bedrock engineering gate: emit every registered xrpl program to WAT/wasm,
# then assert the wasm import table is host_lib and required exports exist.
# Does NOT start rippled / bedrock / AlphaNet (that is wsm-003).
set -euo pipefail
cd "$(dirname "$0")/../.."

OUT=${OUT:-build/xrpl}
lake exe pf -- build --target xrpl --out "$OUT"

python3 - "$OUT" <<'PY'
import sys
from pathlib import Path

out = Path(sys.argv[1])
wats = sorted(out.glob("*.wat"))
wasms = sorted(out.glob("*.wasm"))
if not wats:
    sys.exit("xrpl check: no .wat produced")
if len(wats) != len(wasms):
    sys.exit(f"xrpl check: wat/wasm count mismatch {len(wats)}/{len(wasms)}")

need_imports = (
    '(import "host_lib" "get_current_ledger_obj_field"',
    '(import "host_lib" "get_data_object_field"',
    '(import "host_lib" "set_data_object_field"',
    '(import "host_lib" "function_param"',
    '(import "host_lib" "get_tx_field"',
    '(import "host_lib" "get_ledger_sqn"',
    '(import "host_lib" "get_parent_ledger_time"',
    '(import "host_lib" "compute_sha512_half"',
    '(import "host_lib" "get_parent_ledger_hash"',
    '(import "host_lib" "get_base_fee"',
)
need_exports_counter = (
    '(func (export "initialize") (result i32)',
    '(func (export "increment") (result i32)',
    '(func (export "get")',
)
need_exports_ctx = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "height")',
)
need_exports_own = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
)
need_exports_hash = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "get")',
    '(call $compute_sha512_half',
)
need_exports_rt2 = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(call $get_parent_ledger_hash',
    '(call $get_base_fee)',
)
forbid = ("xrpl_wasm_std", "get_current_contract_call", "(param $pf_p0 i64)", '"update_data"', "eq_account")

for wat in wats:
    text = wat.read_text(encoding="utf-8")
    for needle in need_imports:
        if needle not in text:
            sys.exit(f"xrpl check: {wat.name} missing {needle!r}")
    if wat.stem == "XrplCtx":
        exports = need_exports_ctx
    elif wat.stem == "XrplOwn":
        exports = need_exports_own
    elif wat.stem == "XrplHash":
        exports = need_exports_hash
    elif wat.stem == "XrplRt2":
        exports = need_exports_rt2
    else:
        exports = need_exports_counter
    for needle in exports:
        if needle not in text:
            sys.exit(f"xrpl check: {wat.name} missing {needle!r}")
    for needle in forbid:
        if needle in text:
            sys.exit(f"xrpl check: {wat.name} still contains {needle!r}")
    wasm = out / f"{wat.stem}.wasm"
    if not wasm.is_file() or wasm.stat().st_size == 0:
        sys.exit(f"xrpl check: missing wasm {wasm.name}")
    magic = wasm.read_bytes()[:4]
    if magic != b"\x00asm":
        sys.exit(f"xrpl check: {wasm.name} is not wasm")
    print(f"xrpl check ok: {wat.name} / {wasm.name}")
print("xrpl engineering gate: ok")
PY
