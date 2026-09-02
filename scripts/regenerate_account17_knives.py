#!/usr/bin/env python3
"""Regenerate E∞ knives 121-127 (account-17) from account-16 templates (knives 114-120)."""

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

# Predecessor block currently seeded in account-16 knives (account-15 fields).
ACC15_SUCCESS_TAIL = (
    "account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35 1 0xFA"
)
ACC16_SUCCESS_TAIL = (
    "account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36 1 0xFB"
)
# Abs predecessor in account-16 knives uses 0xBD.
ACC15_ABS_TAIL = "0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35 1 0xFA"
ACC16_ABS_TAIL = "0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36 1 0xFB"


def rename_accounts(text: str) -> str:
    text = text.replace("account16", "__ACC17__")
    text = text.replace("Account16", "__Acc17__")
    text = text.replace("acc16", "__A17__")
    text = text.replace("key16", "__K17__")
    text = text.replace("account15", "account16")
    text = text.replace("Account15", "Account16")
    text = text.replace("acc15", "acc16")
    text = text.replace("key15", "key16")
    text = text.replace("__ACC17__", "account17")
    text = text.replace("__Acc17__", "Account17")
    text = text.replace("__A17__", "acc17")
    text = text.replace("__K17__", "key17")
    return text


def bump_knife_and_sem(text: str) -> str:
    pairs = [
        ("svm-sem-125", "svm-sem-132"), ("svm-sem-124", "svm-sem-131"),
        ("svm-sem-123", "svm-sem-130"), ("svm-sem-122", "svm-sem-129"),
        ("svm-sem-121", "svm-sem-128"), ("svm-sem-120", "svm-sem-127"),
        ("svm-sem-119", "svm-sem-126"),
        ("knife 120", "knife 127"), ("knife 119", "knife 126"),
        ("knife 118", "knife 125"), ("knife 117", "knife 124"),
        ("knife 116", "knife 123"), ("knife 115", "knife 122"),
        ("knife 114", "knife 121"),
        ("Knife 120", "Knife 127"), ("Knife 119", "Knife 126"),
        ("Knife 118", "Knife 125"), ("Knife 117", "Knife 124"),
        ("Knife 116", "Knife 123"), ("Knife 115", "Knife 122"),
        ("Knife 114", "Knife 121"), ("Knife 113", "Knife 120"),
    ]
    for old, new in pairs:
        text = text.replace(old, new)
    return text


def fix_comments(text: str) -> str:
    text = text.replace("Knife 113 completes account-15 fields", "Knife 120 completes account-16 fields")
    text = text.replace("Knife 120 completes account-15 fields", "Knife 120 completes account-16 fields")
    text = text.replace("from the account-15 header cursor", "from the account-16 header cursor")
    text = text.replace("account-15 zero-dataLen", "account-16 zero-dataLen")
    text = text.replace("plus account-15 zero data_len", "plus account-16 zero data_len")
    text = text.replace("account-15 → account-16", "account-16 → account-17")
    text = text.replace("account-16 → account-16", "account-16 → account-17")
    text = text.replace("skip-to-account-16-marker", "skip-to-account-17-marker")
    text = text.replace("sedecuple", "septendecuple")
    text = text.replace(
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15",
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15/16",
    )
    for frag in (
        "meta", "dup", "header", "signer", "lamports", "owner",
        "executable", "exec", "flags", "budget",
    ):
        text = text.replace(f"account-16 {frag}", f"account-17 {frag}")
    text = text.replace("for account-16", "for account-17")
    text = text.replace("on account-16", "on account-17")
    text = text.replace("the account-16", "the account-17")
    text = text.replace("account-16,", "account-17,")
    text = text.replace("account-16 ", "account-17 ")
    text = text.replace("account-16.", "account-17.")
    text = text.replace("account-16)", "account-17)")
    text = text.replace("account-16/", "account-17/")
    return text


def fix_skip_callee(text: str) -> str:
    """Account-16 skip already doubles into ExecRent; rename keeps that shape."""
    marker = "def account16SkipNextInputMem"
    start = text.find(marker)
    if start == -1:
        raise RuntimeError("account16SkipNextInputMem not found after rename")
    end = text.find("\ndef walkAccount16SkipNextAfterSkipChain?", start)
    if end == -1:
        raise RuntimeError("walkAccount16SkipNextAfterSkipChain? not found after rename")
    block = text[start:end]
    if "let m₁ ← account16ExecRentInputMem" not in block:
        raise RuntimeError("skip callee was not renamed to account16ExecRentInputMem")
    if block.count("acc16Marker key16Word") < 2:
        raise RuntimeError("expected doubled acc16 args in skip callee")
    if "storev .m64 m₁ account16DataLenAddr (.vlong 0)" not in block:
        raise RuntimeError("expected zero-store of account16DataLenAddr")
    if "account17HeaderAddr" not in block:
        raise RuntimeError("expected store to account17HeaderAddr")
    return text


def extend_all_skip_chains(text: str) -> str:
    for term in SKIP_TERMINALS:
        if term not in text:
            raise RuntimeError(f"skip terminal not found:\n{term}")
        text = text.replace(term, SKIP_CONT + "\n" + term, 1)
    return text


def update_test_constants(text: str) -> str:
    text = text.replace(ACC15_SUCCESS_TAIL, ACC16_SUCCESS_TAIL)
    text = text.replace(ACC15_ABS_TAIL, ACC16_ABS_TAIL)
    suffix_repl = [
        (
            ACC16_SUCCESS_TAIL
            + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36 1 0xFB",
            ACC16_SUCCESS_TAIL
            + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37 1 0xFC",
        ),
        (
            ACC16_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36 1 0xFB",
            ACC16_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37 1 0xFC",
        ),
        (
            ACC16_SUCCESS_TAIL
            + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36",
            ACC16_SUCCESS_TAIL
            + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37",
        ),
        (
            ACC16_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36",
            ACC16_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37",
        ),
        (
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04",
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05",
        ),
        (
            ACC16_ABS_TAIL + " 0xBE 0x80 1 0 16000 304 0xF3 0x04",
            ACC16_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05",
        ),
        (
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1 16000 304",
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1 17000 320",
        ),
        (
            ACC16_ABS_TAIL + " 0xBE 0x80 1 0 16000 304",
            ACC16_ABS_TAIL + " 0xBF 0x81 1 0 17000 320",
        ),
        (
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x80 1 1",
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1",
        ),
        (ACC16_ABS_TAIL + " 0xBE 0x80 1 0", ACC16_ABS_TAIL + " 0xBF 0x81 1 0"),
        (
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x80\n",
            ACC16_SUCCESS_TAIL + " account0NonDupMarker 0x81\n",
        ),
        (ACC16_ABS_TAIL + " 0xBE 0x80", ACC16_ABS_TAIL + " 0xBF 0x81"),
        (ACC16_ABS_TAIL + " 0xBE\n", ACC16_ABS_TAIL + " 0xBF\n"),
    ]
    for old, new in suffix_repl:
        text = text.replace(old, new)
    repl = [
        ("regs .br2 == 0x80", "regs .br2 == 0x81"),
        ("key == 0x80", "key == 0x81"),
        ("dup == 0xBE && key == 0x81", "dup == 0xBF && key == 0x81"),
        ("marker == 0xBE", "marker == 0xBF"),
        ("dup == 0xBE", "dup == 0xBF"),
        ("regs .br1 == 16000 && regs .br2 == 304", "regs .br1 == 17000 && regs .br2 == 320"),
        ("lamports == 16000 && dataLen == 304", "lamports == 17000 && dataLen == 320"),
        (".vlong 16000)", ".vlong 17000)"),
        ("owner0 == 0xF3 && owner1 == 0x04", "owner0 == 0xF4 && owner1 == 0x05"),
        ("regs .br1 == 0xF3 && regs .br2 == 0x04", "regs .br1 == 0xF4 && regs .br2 == 0x05"),
        (".vlong 0xF3)", ".vlong 0xF4)"),
        ("owner2 == 0x25 && owner3 == 0x36", "owner2 == 0x26 && owner3 == 0x37"),
        ("regs .br1 == 0x25 && regs .br2 == 0x36", "regs .br1 == 0x26 && regs .br2 == 0x37"),
        (".vlong 0x25)", ".vlong 0x26)"),
        ("rent == 0xFB", "rent == 0xFC"),
        ("regs .br2 == 0xFB", "regs .br2 == 0xFC"),
        ("executable_1_rent_0xFB", "executable_1_rent_0xFC"),
        ("after_skip_key_0x80", "after_skip_key_0x81"),
        ("after_skip_owner2_0x25_owner3_0x36", "after_skip_owner2_0x26_owner3_0x37"),
        ("lamports_16000_dataLen_304", "lamports_17000_dataLen_320"),
        (
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x80)",
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x81)",
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
        and "knife 114" in lean_lines[i + 1]
    )
    lean_end = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("end ProofForge.Svm.Solanalib")
    )
    lean_out = transform_lean("".join(lean_lines[lean_start:lean_end]))
    SOLANALIB.write_text(
        "".join(lean_lines[:lean_end]) + lean_out + "end ProofForge.Svm.Solanalib\n"
    )
    print(f"Appended Solanalib account-17: {len(lean_out.splitlines())} lines")

    spec_lines = SPEC.read_text().splitlines(keepends=True)
    spec_start = next(
        i for i, line in enumerate(spec_lines)
        if "knife 114" in line.lower() and "account-16" in line
    )
    end_idx = next(
        i for i, line in enumerate(spec_lines)
        if line.startswith("end Tests.SolanalibSpec")
    )
    spec_out = transform_spec("".join(spec_lines[spec_start:end_idx]))
    SPEC.write_text(
        "".join(spec_lines[:end_idx]) + spec_out + "end Tests.SolanalibSpec\n"
    )
    print(f"Appended Spec account-17: {len(spec_out.splitlines())} lines")


if __name__ == "__main__":
    main()
