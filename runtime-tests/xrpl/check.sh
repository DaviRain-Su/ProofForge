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
    '(call $function_param',
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
    '(call $function_param',
    '(i64.store (i32.const 0)',
)
need_exports_nest = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "get")',
    '(call $function_param',
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
    '(func (export "setAt") (result i32)',
    '(func (export "sum4")',
    '(func (export "get0")',
    '(call $function_param',
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
need_exports_crew = (
    '(func (export "initialize") (result i32)',
    '(func (export "setOp") (result i32)',
    '(func (export "bump") (result i32)',
    '(func (export "get")',
    'i64.eq',
    '(i32.const 3)',
    '(data (i32.const 64) "owner0owner1owner2op0op1op2value")',
)
need_exports_pay = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "pay") (result i32)',
    '(func (export "get")',
    '(call $function_param',
    '(data (i32.const 64) "bal")',
)
need_exports_mint = (
    '(func (export "initialize") (result i32)',
    '(func (export "mint") (result i32)',
    '(func (export "mintTo") (result i32)',
    '(func (export "pay") (result i32)',
    '(func (export "burn") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "unpause") (result i32)',
    '(func (export "setCap") (result i32)',
    '(func (export "approve") (result i32)',
    '(func (export "takeFrom") (result i32)',
    '(func (export "burnFrom") (result i32)',
    '(func (export "clawback") (result i32)',
    '(func (export "freeze") (result i32)',
    '(func (export "unfreeze") (result i32)',
    '(func (export "freezeOf") (result i32)',
    '(func (export "unfreezeOf") (result i32)',
    '(func (export "get")',
    '(i32.const 3)',
    '(i32.const 4)',
    '(i32.const 5)',
    '(call $function_param',
    '(data (i32.const 64) "bal")',
    '(i32.store8 (i32.const 88) (i32.const 115))',
    '(i32.store8 (i32.const 72) (i32.const 99))',
    '(i32.store8 (i32.const 92) (i32.const 97))',
    '(i32.store8 (i32.const 96) (i32.const 108))',
)
need_exports_vault = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "get")',
    '(data (i32.const 64) "bal")',
    '(i32.store8 (i32.const 88) (i32.const 115))',
    '(i32.const 524313)',
)
need_exports_emit = (
    '(func (export "initialize") (result i32)',
    '(func (export "ping") (result i32)',
    '(func (export "get")',
    '(import "host_lib" "build_txn"',
    '(import "host_lib" "emit_built_txn"',
    '(i32.const 393217)',
)
need_exports_tip = (
    '(func (export "initialize") (result i32)',
    '(func (export "ping") (result i32)',
    '(func (export "get")',
    '(import "host_lib" "build_txn"',
    '(import "host_lib" "emit_built_txn"',
    '(i64.const 384)',
)
need_exports_gift = (
    '(func (export "initialize") (result i32)',
    '(func (export "ping") (result i32)',
    '(func (export "get")',
    '(import "host_lib" "build_txn"',
    '(import "host_lib" "emit_built_txn"',
    '(i32.const 208)',
)
need_exports_cash = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "cash") (result i32)',
    '(func (export "get")',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
)
need_exports_bank = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "cash") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "unpause") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
)
need_exports_safe = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "cash") (result i32)',
    '(func (export "freeze") (result i32)',
    '(func (export "unfreeze") (result i32)',
    '(func (export "pause") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
    '(i32.store8 (i32.const 96) (i32.const 108))',
)
need_exports_pool = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "sendToB") (result i32)',
    '(func (export "cashToB") (result i32)',
    '(func (export "freeze") (result i32)',
    '(func (export "pause") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
    '(i32.const 208)',
)
need_exports_fund = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "sendToB") (result i32)',
    '(func (export "cashToB") (result i32)',
    '(func (export "setCap10") (result i32)',
    '(func (export "grantOp") (result i32)',
    '(func (export "pause") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
    '(i32.store8 (i32.const 72) (i32.const 99))',
)
need_exports_treasury = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "sendToB") (result i32)',
    '(func (export "cashSelf") (result i32)',
    '(func (export "clawB") (result i32)',
    '(func (export "burn") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
)
need_exports_payout = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "lockIn") (result i32)',
    '(func (export "cashB") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
    '(i32.store8 (i32.const 76) (i32.const 100))',
    '(i32.store8 (i32.const 100) (i32.const 101))',
)
need_exports_claim = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "lockIn") (result i32)',
    '(func (export "claimB") (result i32)',
    '(i32.const 524313)',
    '(i32.store8 (i32.const 76) (i32.const 100))',
    '(i32.store8 (i32.const 100) (i32.const 101))',
)
need_exports_vest = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "lockIn") (result i32)',
    '(func (export "refund") (result i32)',
    '(i32.const 524313)',
    '(i32.store8 (i32.const 76) (i32.const 100))',
    '(i32.store8 (i32.const 100) (i32.const 101))',
)
need_exports_holdesc = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "lockIn") (result i32)',
    '(func (export "releaseToB") (result i32)',
    '(func (export "refund") (result i32)',
    '(i32.const 524313)',
    '(i32.store8 (i32.const 100) (i32.const 101))',
)
need_exports_take = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "grant") (result i32)',
    '(func (export "takeB") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "freeze") (result i32)',
    '(i32.const 524313)',
    '(i32.store8 (i32.const 92) (i32.const 97))',
)
need_exports_share = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "mintToB") (result i32)',
    '(func (export "cashToB") (result i32)',
    '(func (export "clawB") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "freeze") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
)
need_exports_token = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "sendToB") (result i32)',
    '(func (export "cashSelf") (result i32)',
    '(func (export "clawB") (result i32)',
    '(func (export "burn") (result i32)',
    '(func (export "pause") (result i32)',
    '(func (export "freeze") (result i32)',
    '(i32.const 524313)',
    '(import "host_lib" "emit_built_txn"',
)
need_exports_lock = (
    '(func (export "initialize") (result i32)',
    '(func (export "credit") (result i32)',
    '(func (export "pay") (result i32)',
    '(func (export "freeze") (result i32)',
    '(func (export "unfreeze") (result i32)',
    '(func (export "get")',
    '(i32.const 5)',
    '(call $function_param',
    '(data (i32.const 64) "bal")',
    '(i32.store8 (i32.const 96) (i32.const 108))',
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
    elif wat.stem == "XrplCrew":
        exports = need_exports_crew
    elif wat.stem == "XrplPay":
        exports = need_exports_pay
    elif wat.stem == "XrplMint":
        exports = need_exports_mint
    elif wat.stem == "XrplLock":
        exports = need_exports_lock
    elif wat.stem == "XrplCard":
        exports = need_exports_lock
    elif wat.stem == "XrplVault":
        exports = need_exports_vault
    elif wat.stem == "XrplEmit":
        exports = need_exports_emit
    elif wat.stem == "XrplTip":
        exports = need_exports_tip
    elif wat.stem == "XrplGift":
        exports = need_exports_gift
    elif wat.stem == "XrplCash":
        exports = need_exports_cash
    elif wat.stem == "XrplBank":
        exports = need_exports_bank
    elif wat.stem == "XrplSafe":
        exports = need_exports_safe
    elif wat.stem == "XrplPool":
        exports = need_exports_pool
    elif wat.stem == "XrplFund":
        exports = need_exports_fund
    elif wat.stem == "XrplTreasury":
        exports = need_exports_treasury
    elif wat.stem == "XrplToken":
        exports = need_exports_token
    elif wat.stem == "XrplShare":
        exports = need_exports_share
    elif wat.stem == "XrplTake":
        exports = need_exports_take
    elif wat.stem == "XrplHoldEsc":
        exports = need_exports_holdesc
    elif wat.stem == "XrplVest":
        exports = need_exports_vest
    elif wat.stem == "XrplClaim":
        exports = need_exports_claim
    elif wat.stem == "XrplPayout":
        exports = need_exports_payout
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
