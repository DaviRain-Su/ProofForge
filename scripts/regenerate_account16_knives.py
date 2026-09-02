#!/usr/bin/env python3
"""Regenerate E∞ knives 114-120 (account-16) from account-15 templates (knives 107-113)."""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOLANALIB = ROOT / "ProofForge/Svm/Solanalib.lean"
SPEC = ROOT / "Tests/SolanalibSpec.lean"

SKIP_CONT = """    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),"""

SKIP_TERMINALS = [
    "    .ldx .m8 .br1 .br2 zeroOff,\n    .st .m64 .br10",
    "    .ldx .m8 .br1 .br2 zeroOff,\n    .ldx .m64 .br4 .br2 keyOff",
    "    .ldx .m8 .br1 .br2 signerOff,",
    "    .ldx .m64 .br1 .br2 lamportsOff,",
    "    .ldx .m64 .br1 .br2 owner0Off,",
    "    .ldx .m64 .br1 .br2 owner2Off,",
    "    .ldx .m8 .br1 .br2 execOff,",
]

# Predecessor block currently seeded in account-15 knives (account-14 fields).
ACC14_SUCCESS_TAIL = (
    "account0NonDupMarker 0x7E 1 1 14000 272 0xF1 0x02 0x23 0x34 1 0xF9"
)
ACC15_SUCCESS_TAIL = (
    "account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35 1 0xFA"
)
# Abs predecessor in account-15 knives uses 0xBB (not 0xBC).
ACC14_ABS_TAIL = "0xBB 0x7E 1 0 14000 272 0xF1 0x02 0x23 0x34 1 0xF9"
ACC15_ABS_TAIL = "0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35 1 0xFA"


def rename_accounts(text: str) -> str:
    text = text.replace("account15", "__ACC16__")
    text = text.replace("Account15", "__Acc16__")
    text = text.replace("acc15", "__A16__")
    text = text.replace("key15", "__K16__")
    text = text.replace("account14", "account15")
    text = text.replace("Account14", "Account15")
    text = text.replace("acc14", "acc15")
    text = text.replace("key14", "key15")
    text = text.replace("__ACC16__", "account16")
    text = text.replace("__Acc16__", "Account16")
    text = text.replace("__A16__", "acc16")
    text = text.replace("__K16__", "key16")
    return text


def bump_knife_and_sem(text: str) -> str:
    pairs = [
        ("svm-sem-118", "svm-sem-125"), ("svm-sem-117", "svm-sem-124"),
        ("svm-sem-116", "svm-sem-123"), ("svm-sem-115", "svm-sem-122"),
        ("svm-sem-114", "svm-sem-121"), ("svm-sem-113", "svm-sem-120"),
        ("svm-sem-112", "svm-sem-119"),
        ("knife 113", "knife 120"), ("knife 112", "knife 119"),
        ("knife 111", "knife 118"), ("knife 110", "knife 117"),
        ("knife 109", "knife 116"), ("knife 108", "knife 115"),
        ("knife 107", "knife 114"),
        ("Knife 113", "Knife 120"), ("Knife 112", "Knife 119"),
        ("Knife 111", "Knife 118"), ("Knife 110", "Knife 117"),
        ("Knife 109", "Knife 116"), ("Knife 108", "Knife 115"),
        ("Knife 107", "Knife 114"), ("Knife 106", "Knife 113"),
    ]
    for old, new in pairs:
        text = text.replace(old, new)
    return text


def fix_comments(text: str) -> str:
    text = text.replace("Knife 106 completes account-14 fields", "Knife 113 completes account-15 fields")
    text = text.replace("Knife 113 completes account-14 fields", "Knife 113 completes account-15 fields")
    text = text.replace("from the account-14 header cursor", "from the account-15 header cursor")
    text = text.replace("account-14 zero-dataLen", "account-15 zero-dataLen")
    text = text.replace("plus account-14 zero data_len", "plus account-15 zero data_len")
    text = text.replace("account-14 → account-15", "account-15 → account-16")
    text = text.replace("account-15 → account-15", "account-15 → account-16")
    text = text.replace("skip-to-account-15-marker", "skip-to-account-16-marker")
    text = text.replace("quindecuple", "sedecuple")
    text = text.replace(
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14",
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15",
    )
    for frag in (
        "meta", "dup", "header", "signer", "lamports", "owner",
        "executable", "exec", "flags", "budget",
    ):
        text = text.replace(f"account-15 {frag}", f"account-16 {frag}")
    text = text.replace("for account-15", "for account-16")
    text = text.replace("on account-15", "on account-16")
    text = text.replace("the account-15", "the account-16")
    text = text.replace("account-15,", "account-16,")
    text = text.replace("account-15 ", "account-16 ")
    text = text.replace("account-15.", "account-16.")
    text = text.replace("account-15)", "account-16)")
    text = text.replace("account-15/", "account-16/")
    return text


def fix_skip_callee(text: str) -> str:
    """Account-15 skip already doubles into ExecRent; rename keeps that shape.

    After rename, account15SkipNextInputMem already calls account15ExecRentInputMem
    with doubled acc15 args, zeroes account15DataLenAddr, and stores account16 marker.
    Do not add another doubling (that would triple the trailing params).
    """
    marker = "def account15SkipNextInputMem"
    start = text.find(marker)
    if start == -1:
        raise RuntimeError("account15SkipNextInputMem not found after rename")
    end = text.find("\ndef walkAccount15SkipNextAfterSkipChain?", start)
    if end == -1:
        raise RuntimeError("walkAccount15SkipNextAfterSkipChain? not found after rename")
    block = text[start:end]
    if "let m₁ ← account15ExecRentInputMem" not in block:
        raise RuntimeError("skip callee was not renamed to account15ExecRentInputMem")
    if block.count("acc15Marker key15Word") < 2:
        raise RuntimeError("expected doubled acc15 args in skip callee")
    if "storev .m64 m₁ account15DataLenAddr (.vlong 0)" not in block:
        raise RuntimeError("expected zero-store of account15DataLenAddr")
    if "account16HeaderAddr" not in block:
        raise RuntimeError("expected store to account16HeaderAddr")
    return text


def extend_all_skip_chains(text: str) -> str:
    for term in SKIP_TERMINALS:
        if term not in text:
            raise RuntimeError(f"skip terminal not found:\n{term}")
        text = text.replace(term, SKIP_CONT + "\n" + term, 1)
    return text


def update_test_constants(text: str) -> str:
    # Promote predecessor account-14 seeded block → account-15 seeded block.
    text = text.replace(ACC14_SUCCESS_TAIL, ACC15_SUCCESS_TAIL)
    text = text.replace(ACC14_ABS_TAIL, ACC15_ABS_TAIL)
    # Replace account-16 target tails; prefix with ACC15 seed so we never corrupt it.
    suffix_repl = [
        (
            ACC15_SUCCESS_TAIL
            + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35 1 0xFA",
            ACC15_SUCCESS_TAIL
            + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36 1 0xFB",
        ),
        (
            ACC15_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35 1 0xFA",
            ACC15_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36 1 0xFB",
        ),
        (
            ACC15_SUCCESS_TAIL
            + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35",
            ACC15_SUCCESS_TAIL
            + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36",
        ),
        (
            ACC15_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35",
            ACC15_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36",
        ),
        (
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03",
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04",
        ),
        (
            ACC15_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03",
            ACC15_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04",
        ),
        (
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1 15000 288",
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1 16000 304",
        ),
        (
            ACC15_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288",
            ACC15_ABS_TAIL + " 0xBE 0x80 1 0 16000 304",
        ),
        (
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1",
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1",
        ),
        (ACC15_ABS_TAIL + " 0xBD 0x7F 1 0", ACC15_ABS_TAIL + " 0xBE 0x80 1 0"),
        (
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x7F\n",
            ACC15_SUCCESS_TAIL + " account0NonDupMarker 0x80\n",
        ),
        (ACC15_ABS_TAIL + " 0xBD 0x7F", ACC15_ABS_TAIL + " 0xBE 0x80"),
        (ACC15_ABS_TAIL + " 0xBD\n", ACC15_ABS_TAIL + " 0xBE\n"),
    ]
    for old, new in suffix_repl:
        text = text.replace(old, new)
    repl = [
        ("regs .br2 == 0x7F", "regs .br2 == 0x80"),
        ("key == 0x7F", "key == 0x80"),
        ("dup == 0xBD && key == 0x80", "dup == 0xBE && key == 0x80"),
        ("marker == 0xBD", "marker == 0xBE"),
        ("dup == 0xBD", "dup == 0xBE"),
        ("regs .br1 == 15000 && regs .br2 == 288", "regs .br1 == 16000 && regs .br2 == 304"),
        ("lamports == 15000 && dataLen == 288", "lamports == 16000 && dataLen == 304"),
        (".vlong 15000)", ".vlong 16000)"),
        ("owner0 == 0xF2 && owner1 == 0x03", "owner0 == 0xF3 && owner1 == 0x04"),
        ("regs .br1 == 0xF2 && regs .br2 == 0x03", "regs .br1 == 0xF3 && regs .br2 == 0x04"),
        (".vlong 0xF2)", ".vlong 0xF3)"),
        ("owner2 == 0x24 && owner3 == 0x35", "owner2 == 0x25 && owner3 == 0x36"),
        ("regs .br1 == 0x24 && regs .br2 == 0x35", "regs .br1 == 0x25 && regs .br2 == 0x36"),
        (".vlong 0x24)", ".vlong 0x25)"),
        ("rent == 0xFA", "rent == 0xFB"),
        ("regs .br2 == 0xFA", "regs .br2 == 0xFB"),
        ("executable_1_rent_0xFA", "executable_1_rent_0xFB"),
        ("after_skip_key_0x7F", "after_skip_key_0x80"),
        ("after_skip_owner2_0x24_owner3_0x35", "after_skip_owner2_0x25_owner3_0x36"),
        ("lamports_15000_dataLen_288", "lamports_16000_dataLen_304"),
        (
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x7F)",
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x80)",
        ),
    ]
    for old, new in repl:
        text = text.replace(old, new)
    return text


def transform_lean(text: str) -> str:
    text = rename_accounts(text)
    text = bump_knife_and_sem(text)
    text = fix_comments(text)
    text = fix_skip_callee(text)
    text = extend_all_skip_chains(text)
    text = update_test_constants(text)
    return text


def transform_spec(text: str) -> str:
    text = rename_accounts(text)
    text = bump_knife_and_sem(text)
    text = fix_comments(text)
    text = update_test_constants(text)
    return text


def main() -> None:
    lean_lines = SOLANALIB.read_text().splitlines(keepends=True)
    lean_start = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("/-!")
        and i + 1 < len(lean_lines)
        and "knife 107" in lean_lines[i + 1]
    )
    lean_end = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("end ProofForge.Svm.Solanalib")
    )
    lean_out = transform_lean("".join(lean_lines[lean_start:lean_end]))
    SOLANALIB.write_text(
        "".join(lean_lines[:lean_end]) + lean_out + "end ProofForge.Svm.Solanalib\n"
    )
    print(f"Appended Solanalib account-16: {len(lean_out.splitlines())} lines")

    spec_lines = SPEC.read_text().splitlines(keepends=True)
    spec_start = next(
        i for i, line in enumerate(spec_lines)
        if "knife 107" in line.lower() and "account-15" in line
    )
    end_idx = next(
        i for i, line in enumerate(spec_lines)
        if line.startswith("end Tests.SolanalibSpec")
    )
    spec_out = transform_spec("".join(spec_lines[spec_start:end_idx]))
    SPEC.write_text(
        "".join(spec_lines[:end_idx]) + spec_out + "end Tests.SolanalibSpec\n"
    )
    print(f"Appended Spec account-16: {len(spec_out.splitlines())} lines")


if __name__ == "__main__":
    main()
