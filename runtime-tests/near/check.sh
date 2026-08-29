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
    '(func (export "get")',
)
counter_exports = (
    '(func (export "increment")',
)
ctx_imports = (
    '(import "env" "block_index"',
    '(import "env" "block_timestamp"',
    '(import "env" "predecessor_account_id"',
    '(import "env" "attached_deposit"',
    '(import "env" "account_balance"',
    '(import "env" "current_account_id"',
    '(import "env" "log_utf8"',
)
ctx_exports = (
    '(func (export "height")',
    '(func (export "seconds")',
    '(func (export "selfBal")',
    '(func (export "selfBalHigh")',
    '(func (export "takeDeposit")',
    '(func (export "takeDepositHigh")',
    '(func (export "takeDepositLegacy")',
    '(func (export "logReady")',
    '(func (export "logView")',
    '(func (export "selfId")',
    '(func (export "selfIdLength")',
    '(func (export "selfIdWord1")',
    '(func (export "checkSelfCall")',
)
bytes_anchors = (
    '(func $pf_utf8_valid',
    '(func (export "inspectBytes")',
    '(func (export "inspectString")',
    '(call $pf_utf8_valid (i32.const 260)',
)
memory_anchors = (
    '(func $pf_arena_reset',
    '(func $pf_arena_alloc',
    'memory.grow',
    '(func $pf_buffer64_begin',
    '(func $pf_buffer64_get',
    '(func (export "roundTrip")',
    '(func (export "growAndReuse")',
)
forbid = ("host_lib", "xrpl_wasm_std", "get_current_contract_call")

for wat in wats:
    text = wat.read_text(encoding="utf-8")
    extra = ()
    if wat.stem == "Counter":
        extra = counter_exports
    elif wat.stem == "NearCtx":
        extra = ctx_imports + ctx_exports
    elif wat.stem == "NearBytes":
        extra = bytes_anchors
    elif wat.stem == "NearMemory":
        extra = memory_anchors
    for needle in need_imports + need_exports + extra:
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
