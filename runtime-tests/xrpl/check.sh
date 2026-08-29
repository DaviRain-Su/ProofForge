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
if not wats:
    sys.exit("xrpl check: no .wat produced")
# Ignore leftover probe wasm (e.g. probe-array.wasm) that has no matching WAT.

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
need_exports_vec = (
    '(func (export "initialize") (result i32)',
    '(func (export "setAt") (result i32)',
    '(func (export "get0")',
    '(data (i32.const 64) "xs_0xs_1xs_2")',
)
need_exports_smoke = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "get")',
)
need_exports_gate = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "renounce") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
)
need_exports_hold = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "unpause") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
    '(i32.const 4)',
)
need_exports_mark = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "renounce") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
    '(call $compute_sha512_half',
)
need_exports_bal = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "bal")',
)
need_exports_balrt = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "drops")',
)
need_exports_root = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "getSeq")',
    '(data (i32.const 64) "seqflagsownc")',
)
need_exports_tx = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "getSeq")',
    '(data (i32.const 64) "tseqtfee")',
)
need_exports_send = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "bal")',
    '(i32.store8 (i32.const 0) (i32.const 208))',
)
need_exports_nest = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "userbal")',
)
need_exports_step = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "propose") (result i32)',
    '(func (export "accept") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
    '(data (i32.const 64) "owner0owner1owner2pend0pend1pend2value")',
)
need_exports_role = (
    '(func (export "initialize") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "setOp") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
    '(data (i32.const 64) "owner0owner1owner2op0op1op2value")',
)
need_exports_peer = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "drops")',
)
need_exports_flag = (
    '(func (export "initialize") (result i32)',
    '(func (export "stamp") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "flags")',
)
need_exports_tab = (
    '(func (export "initialize") (result i32)',
    '(func (export "fill0") (result i32)',
    '(func (export "sum4")',
    '(func (export "get0")',
    '(data (i32.const 64) "xs_0xs_1xs_2xs_3")',
)
need_exports_hand = (
    '(func (export "initialize") (result i32)',
    '(func (export "propose") (result i32)',
    '(func (export "accept") (result i32)',
    '(func (export "bump") (result i32)',
    'i64.eq',
    '(i32.const 3)',
    '(data (i32.const 64) "owner0owner1owner2pend0pend1pend2value")',
)
forbid = ("xrpl_wasm_std", "get_current_contract_call", "(param $pf_p0 i64)", '"update_data"', "eq_account", "set_data_array_element_field")

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
    elif wat.stem == "XrplVec":
        exports = need_exports_vec
    elif wat.stem == "XrplSmoke":
        exports = need_exports_smoke
    elif wat.stem == "XrplGate":
        exports = need_exports_gate
    elif wat.stem == "XrplHold":
        exports = need_exports_hold
    elif wat.stem == "XrplMark":
        exports = need_exports_mark
    elif wat.stem == "XrplBal":
        exports = need_exports_bal
    elif wat.stem == "XrplBalRt":
        exports = need_exports_balrt
    elif wat.stem == "XrplRoot":
        exports = need_exports_root
    elif wat.stem == "XrplTx":
        exports = need_exports_tx
    elif wat.stem == "XrplSend":
        exports = need_exports_send
    elif wat.stem == "XrplNest":
        exports = need_exports_nest
    elif wat.stem == "XrplStep":
        exports = need_exports_step
    elif wat.stem == "XrplRole":
        exports = need_exports_role
    elif wat.stem == "XrplPeer":
        exports = need_exports_peer
    elif wat.stem == "XrplFlag":
        exports = need_exports_flag
    elif wat.stem == "XrplTab":
        exports = need_exports_tab
    elif wat.stem == "XrplHand":
        exports = need_exports_hand
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
