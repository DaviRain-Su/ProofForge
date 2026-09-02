#!/usr/bin/env python3
"""Regenerate E∞ knives 128-134 (account-18) from account-17 templates (knives 121-127)."""

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

# Predecessor block currently seeded in account-17 knives (account-16 fields).
ACC16_SUCCESS_TAIL = (
    "account0NonDupMarker 0x80 1 1 16000 304 0xF3 0x04 0x25 0x36 1 0xFB"
)
ACC17_SUCCESS_TAIL = (
    "account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37 1 0xFC"
)
# Abs predecessor in account-17 knives uses 0xBE for the account-16-shaped abs block.
ACC16_ABS_TAIL = "0xBE 0x80 1 0 16000 304 0xF3 0x04 0x25 0x36 1 0xFB"
ACC17_ABS_TAIL = "0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37 1 0xFC"


def rename_accounts(text: str) -> str:
    text = text.replace("account17", "__ACC18__")
    text = text.replace("Account17", "__Acc18__")
    text = text.replace("acc17", "__A18__")
    text = text.replace("key17", "__K18__")
    text = text.replace("account16", "account17")
    text = text.replace("Account16", "Account17")
    text = text.replace("acc16", "acc17")
    text = text.replace("key16", "key17")
    text = text.replace("__ACC18__", "account18")
    text = text.replace("__Acc18__", "Account18")
    text = text.replace("__A18__", "acc18")
    text = text.replace("__K18__", "key18")
    return text


def bump_knife_and_sem(text: str) -> str:
    pairs = [
        ("svm-sem-132", "svm-sem-139"), ("svm-sem-131", "svm-sem-138"),
        ("svm-sem-130", "svm-sem-137"), ("svm-sem-129", "svm-sem-136"),
        ("svm-sem-128", "svm-sem-135"), ("svm-sem-127", "svm-sem-134"),
        ("svm-sem-126", "svm-sem-133"),
        ("knife 127", "knife 134"), ("knife 126", "knife 133"),
        ("knife 125", "knife 132"), ("knife 124", "knife 131"),
        ("knife 123", "knife 130"), ("knife 122", "knife 129"),
        ("knife 121", "knife 128"),
        ("Knife 127", "Knife 134"), ("Knife 126", "Knife 133"),
        ("Knife 125", "Knife 132"), ("Knife 124", "Knife 131"),
        ("Knife 123", "Knife 130"), ("Knife 122", "Knife 129"),
        ("Knife 121", "Knife 128"), ("Knife 120", "Knife 127"),
    ]
    for old, new in pairs:
        text = text.replace(old, new)
    return text


def fix_comments(text: str) -> str:
    text = text.replace("Knife 120 completes account-16 fields", "Knife 127 completes account-17 fields")
    text = text.replace("Knife 127 completes account-16 fields", "Knife 127 completes account-17 fields")
    text = text.replace("from the account-16 header cursor", "from the account-17 header cursor")
    text = text.replace("account-16 zero-dataLen", "account-17 zero-dataLen")
    text = text.replace("plus account-16 zero data_len", "plus account-17 zero data_len")
    text = text.replace("account-16 → account-17", "account-17 → account-18")
    text = text.replace("account-17 → account-17", "account-17 → account-18")
    text = text.replace("skip-to-account-17-marker", "skip-to-account-18-marker")
    text = text.replace("septendecuple", "octodecuple")
    text = text.replace(
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15/16",
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15/16/17",
    )
    for frag in (
        "meta", "dup", "header", "signer", "lamports", "owner",
        "executable", "exec", "flags", "budget",
    ):
        text = text.replace(f"account-17 {frag}", f"account-18 {frag}")
    text = text.replace("for account-17", "for account-18")
    text = text.replace("on account-17", "on account-18")
    text = text.replace("the account-17", "the account-18")
    text = text.replace("account-17,", "account-18,")
    text = text.replace("account-17 ", "account-18 ")
    text = text.replace("account-17.", "account-18.")
    text = text.replace("account-17)", "account-18)")
    text = text.replace("account-17/", "account-18/")
    return text


def fix_skip_callee(text: str) -> str:
    """Account-17 skip already doubles into ExecRent; rename keeps that shape."""
    marker = "def account17SkipNextInputMem"
    start = text.find(marker)
    if start == -1:
        raise RuntimeError("account17SkipNextInputMem not found after rename")
    end = text.find("\ndef walkAccount17SkipNextAfterSkipChain?", start)
    if end == -1:
        raise RuntimeError("walkAccount17SkipNextAfterSkipChain? not found after rename")
    block = text[start:end]
    if "let m₁ ← account17ExecRentInputMem" not in block:
        raise RuntimeError("skip callee was not renamed to account17ExecRentInputMem")
    if block.count("acc17Marker key17Word") < 2:
        raise RuntimeError("expected doubled acc17 args in skip callee")
    if "storev .m64 m₁ account17DataLenAddr (.vlong 0)" not in block:
        raise RuntimeError("expected zero-store of account17DataLenAddr")
    if "account18HeaderAddr" not in block:
        raise RuntimeError("expected store to account18HeaderAddr")
    return text


def extend_all_skip_chains(text: str) -> str:
    for term in SKIP_TERMINALS:
        if term not in text:
            raise RuntimeError(f"skip terminal not found:\n{term}")
        text = text.replace(term, SKIP_CONT + "\n" + term, 1)
    return text


def update_test_constants(text: str) -> str:
    text = text.replace(ACC16_SUCCESS_TAIL, ACC17_SUCCESS_TAIL)
    text = text.replace(ACC16_ABS_TAIL, ACC17_ABS_TAIL)
    suffix_repl = [
        (
            ACC17_SUCCESS_TAIL
            + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37 1 0xFC",
            ACC17_SUCCESS_TAIL
            + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06 0x27 0x38 1 0xFD",
        ),
        (
            ACC17_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37 1 0xFC",
            ACC17_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06 0x27 0x38 1 0xFD",
        ),
        (
            ACC17_SUCCESS_TAIL
            + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37",
            ACC17_SUCCESS_TAIL
            + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06 0x27 0x38",
        ),
        (
            ACC17_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37",
            ACC17_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06 0x27 0x38",
        ),
        (
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05",
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06",
        ),
        (
            ACC17_ABS_TAIL + " 0xBF 0x81 1 0 17000 320 0xF4 0x05",
            ACC17_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06",
        ),
        (
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1 17000 320",
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1 18000 336",
        ),
        (
            ACC17_ABS_TAIL + " 0xBF 0x81 1 0 17000 320",
            ACC17_ABS_TAIL + " 0xC0 0x82 1 0 18000 336",
        ),
        (
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x81 1 1",
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1",
        ),
        (ACC17_ABS_TAIL + " 0xBF 0x81 1 0", ACC17_ABS_TAIL + " 0xC0 0x82 1 0"),
        (
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x81\n",
            ACC17_SUCCESS_TAIL + " account0NonDupMarker 0x82\n",
        ),
        (ACC17_ABS_TAIL + " 0xBF 0x81", ACC17_ABS_TAIL + " 0xC0 0x82"),
        (ACC17_ABS_TAIL + " 0xBF\n", ACC17_ABS_TAIL + " 0xC0\n"),
    ]
    for old, new in suffix_repl:
        text = text.replace(old, new)
    repl = [
        ("regs .br2 == 0x81", "regs .br2 == 0x82"),
        ("key == 0x81", "key == 0x82"),
        ("dup == 0xBF && key == 0x82", "dup == 0xC0 && key == 0x82"),
        ("marker == 0xBF", "marker == 0xC0"),
        ("dup == 0xBF", "dup == 0xC0"),
        ("regs .br1 == 17000 && regs .br2 == 320", "regs .br1 == 18000 && regs .br2 == 336"),
        ("lamports == 17000 && dataLen == 320", "lamports == 18000 && dataLen == 336"),
        (".vlong 17000)", ".vlong 18000)"),
        ("owner0 == 0xF4 && owner1 == 0x05", "owner0 == 0xF5 && owner1 == 0x06"),
        ("regs .br1 == 0xF4 && regs .br2 == 0x05", "regs .br1 == 0xF5 && regs .br2 == 0x06"),
        (".vlong 0xF4)", ".vlong 0xF5)"),
        ("owner2 == 0x26 && owner3 == 0x37", "owner2 == 0x27 && owner3 == 0x38"),
        ("regs .br1 == 0x26 && regs .br2 == 0x37", "regs .br1 == 0x27 && regs .br2 == 0x38"),
        (".vlong 0x26)", ".vlong 0x27)"),
        ("rent == 0xFC", "rent == 0xFD"),
        ("regs .br2 == 0xFC", "regs .br2 == 0xFD"),
        ("executable_1_rent_0xFC", "executable_1_rent_0xFD"),
        ("after_skip_key_0x81", "after_skip_key_0x82"),
        ("after_skip_owner2_0x26_owner3_0x37", "after_skip_owner2_0x27_owner3_0x38"),
        ("lamports_17000_dataLen_320", "lamports_18000_dataLen_336"),
        (
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x81)",
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x82)",
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
        and "knife 121" in lean_lines[i + 1]
    )
    lean_end = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("end ProofForge.Svm.Solanalib")
    )
    lean_out = transform_lean("".join(lean_lines[lean_start:lean_end]))
    SOLANALIB.write_text(
        "".join(lean_lines[:lean_end]) + lean_out + "end ProofForge.Svm.Solanalib\n"
    )
    print(f"Appended Solanalib account-18: {len(lean_out.splitlines())} lines")

    spec_lines = SPEC.read_text().splitlines(keepends=True)
    spec_start = next(
        i for i, line in enumerate(spec_lines)
        if "knife 121" in line.lower() and "account-17" in line
    )
    end_idx = next(
        i for i, line in enumerate(spec_lines)
        if line.startswith("end Tests.SolanalibSpec")
    )
    spec_out = transform_spec("".join(spec_lines[spec_start:end_idx]))
    SPEC.write_text(
        "".join(spec_lines[:end_idx]) + spec_out + "end Tests.SolanalibSpec\n"
    )
    print(f"Appended Spec account-18: {len(spec_out.splitlines())} lines")


if __name__ == "__main__":
    main()
