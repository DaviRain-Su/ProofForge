#!/usr/bin/env python3
"""Regenerate E∞ knives 135-141 (account-19) from account-18 templates (knives 128-134).

Default: skip-only (knife 135 / svm-sem-140). Pass --all for the full field arc.
"""

from pathlib import Path
import sys

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

# Predecessor block currently seeded in account-18 knives (account-17 fields).
ACC17_SUCCESS_TAIL = (
    "account0NonDupMarker 0x81 1 1 17000 320 0xF4 0x05 0x26 0x37 1 0xFC"
)
ACC18_SUCCESS_TAIL = (
    "account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06 0x27 0x38 1 0xFD"
)
# Abs predecessor in account-18 knives uses 0xBF for the account-17-shaped abs block.
ACC17_ABS_TAIL = "0xBF 0x81 1 0 17000 320 0xF4 0x05 0x26 0x37 1 0xFC"
ACC18_ABS_TAIL = "0xC0 0x82 1 0 18000 336 0xF5 0x06 0x27 0x38 1 0xFD"


def rename_accounts(text: str) -> str:
    text = text.replace("account18", "__ACC19__")
    text = text.replace("Account18", "__Acc19__")
    text = text.replace("acc18", "__A19__")
    text = text.replace("key18", "__K19__")
    text = text.replace("account17", "account18")
    text = text.replace("Account17", "Account18")
    text = text.replace("acc17", "acc18")
    text = text.replace("key17", "key18")
    text = text.replace("__ACC19__", "account19")
    text = text.replace("__Acc19__", "Account19")
    text = text.replace("__A19__", "acc19")
    text = text.replace("__K19__", "key19")
    return text


def bump_knife_and_sem(text: str) -> str:
    pairs = [
        ("svm-sem-139", "svm-sem-146"), ("svm-sem-138", "svm-sem-145"),
        ("svm-sem-137", "svm-sem-144"), ("svm-sem-136", "svm-sem-143"),
        ("svm-sem-135", "svm-sem-142"), ("svm-sem-134", "svm-sem-141"),
        ("svm-sem-133", "svm-sem-140"),
        ("knife 134", "knife 141"), ("knife 133", "knife 140"),
        ("knife 132", "knife 139"), ("knife 131", "knife 138"),
        ("knife 130", "knife 137"), ("knife 129", "knife 136"),
        ("knife 128", "knife 135"),
        ("Knife 134", "Knife 141"), ("Knife 133", "Knife 140"),
        ("Knife 132", "Knife 139"), ("Knife 131", "Knife 138"),
        ("Knife 130", "Knife 137"), ("Knife 129", "Knife 136"),
        ("Knife 128", "Knife 135"), ("Knife 127", "Knife 134"),
    ]
    for old, new in pairs:
        text = text.replace(old, new)
    return text


def fix_comments(text: str) -> str:
    # Protect arrow phrases so later `account-18 ` rewrites cannot collapse them.
    text = text.replace("account-17 → account-18", "__ACC_ARROW__")
    text = text.replace("account-18 → account-18", "__ACC_ARROW__")
    text = text.replace("Knife 127 completes account-17 fields", "Knife 134 completes account-18 fields")
    text = text.replace("Knife 134 completes account-17 fields", "Knife 134 completes account-18 fields")
    text = text.replace("from the account-17 header cursor", "from the account-18 header cursor")
    text = text.replace("account-17 zero-dataLen", "account-18 zero-dataLen")
    text = text.replace("plus account-17 zero data_len", "plus account-18 zero data_len")
    text = text.replace("skip-to-account-18-marker", "skip-to-account-19-marker")
    text = text.replace("octodecuple", "nonadecuple")
    text = text.replace(
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15/16/17",
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15/16/17/18",
    )
    for frag in (
        "meta", "dup", "header", "signer", "lamports", "owner",
        "executable", "exec", "flags", "budget",
    ):
        text = text.replace(f"account-18 {frag}", f"account-19 {frag}")
    text = text.replace("for account-18", "for account-19")
    text = text.replace("on account-18", "on account-19")
    text = text.replace("the account-18", "the account-19")
    text = text.replace("account-18,", "account-19,")
    text = text.replace("account-18 ", "account-19 ")
    text = text.replace("account-18.", "account-19.")
    text = text.replace("account-18)", "account-19)")
    text = text.replace("account-18/", "account-19/")
    text = text.replace("__ACC_ARROW__", "account-18 → account-19")
    return text


def fix_skip_callee(text: str) -> str:
    """Account-18 skip already doubles into ExecRent; rename keeps that shape."""
    marker = "def account18SkipNextInputMem"
    start = text.find(marker)
    if start == -1:
        raise RuntimeError("account18SkipNextInputMem not found after rename")
    end = text.find("\ndef walkAccount18SkipNextAfterSkipChain?", start)
    if end == -1:
        raise RuntimeError("walkAccount18SkipNextAfterSkipChain? not found after rename")
    block = text[start:end]
    if "let m₁ ← account18ExecRentInputMem" not in block:
        raise RuntimeError("skip callee was not renamed to account18ExecRentInputMem")
    if block.count("acc18Marker key18Word") < 2:
        raise RuntimeError("expected doubled acc18 args in skip callee")
    if "storev .m64 m₁ account18DataLenAddr (.vlong 0)" not in block:
        raise RuntimeError("expected zero-store of account18DataLenAddr")
    if "account19HeaderAddr" not in block:
        raise RuntimeError("expected store to account19HeaderAddr")
    return text


def extend_all_skip_chains(text: str, *, require_all: bool = True) -> str:
    found = 0
    for term in SKIP_TERMINALS:
        if term not in text:
            if require_all:
                raise RuntimeError(f"skip terminal not found:\n{term}")
            continue
        text = text.replace(term, SKIP_CONT + "\n" + term, 1)
        found += 1
    if found == 0:
        raise RuntimeError("no skip terminals found to extend")
    return text


def update_test_constants(text: str) -> str:
    text = text.replace(ACC17_SUCCESS_TAIL, ACC18_SUCCESS_TAIL)
    text = text.replace(ACC17_ABS_TAIL, ACC18_ABS_TAIL)
    suffix_repl = [
        (
            ACC18_SUCCESS_TAIL
            + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06 0x27 0x38 1 0xFD",
            ACC18_SUCCESS_TAIL
            + " account0NonDupMarker 0x83 1 1 19000 352 0xF6 0x07 0x28 0x39 1 0xFE",
        ),
        (
            ACC18_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06 0x27 0x38 1 0xFD",
            ACC18_ABS_TAIL + " 0xC1 0x83 1 0 19000 352 0xF6 0x07 0x28 0x39 1 0xFE",
        ),
        (
            ACC18_SUCCESS_TAIL
            + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06 0x27 0x38",
            ACC18_SUCCESS_TAIL
            + " account0NonDupMarker 0x83 1 1 19000 352 0xF6 0x07 0x28 0x39",
        ),
        (
            ACC18_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06 0x27 0x38",
            ACC18_ABS_TAIL + " 0xC1 0x83 1 0 19000 352 0xF6 0x07 0x28 0x39",
        ),
        (
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1 18000 336 0xF5 0x06",
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x83 1 1 19000 352 0xF6 0x07",
        ),
        (
            ACC18_ABS_TAIL + " 0xC0 0x82 1 0 18000 336 0xF5 0x06",
            ACC18_ABS_TAIL + " 0xC1 0x83 1 0 19000 352 0xF6 0x07",
        ),
        (
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1 18000 336",
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x83 1 1 19000 352",
        ),
        (
            ACC18_ABS_TAIL + " 0xC0 0x82 1 0 18000 336",
            ACC18_ABS_TAIL + " 0xC1 0x83 1 0 19000 352",
        ),
        (
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x82 1 1",
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x83 1 1",
        ),
        (ACC18_ABS_TAIL + " 0xC0 0x82 1 0", ACC18_ABS_TAIL + " 0xC1 0x83 1 0"),
        (
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x82\n",
            ACC18_SUCCESS_TAIL + " account0NonDupMarker 0x83\n",
        ),
        (ACC18_ABS_TAIL + " 0xC0 0x82", ACC18_ABS_TAIL + " 0xC1 0x83"),
        (ACC18_ABS_TAIL + " 0xC0)", ACC18_ABS_TAIL + " 0xC1)"),
        (ACC18_ABS_TAIL + " 0xC0\n", ACC18_ABS_TAIL + " 0xC1\n"),
    ]
    for old, new in suffix_repl:
        text = text.replace(old, new)
    repl = [
        ("regs .br2 == 0x82", "regs .br2 == 0x83"),
        ("key == 0x82", "key == 0x83"),
        ("dup == 0xC0 && key == 0x83", "dup == 0xC1 && key == 0x83"),
        ("marker == 0xC0", "marker == 0xC1"),
        ("dup == 0xC0", "dup == 0xC1"),
        ("regs .br1 == 18000 && regs .br2 == 336", "regs .br1 == 19000 && regs .br2 == 352"),
        ("lamports == 18000 && dataLen == 336", "lamports == 19000 && dataLen == 352"),
        (".vlong 18000)", ".vlong 19000)"),
        ("owner0 == 0xF5 && owner1 == 0x06", "owner0 == 0xF6 && owner1 == 0x07"),
        ("regs .br1 == 0xF5 && regs .br2 == 0x06", "regs .br1 == 0xF6 && regs .br2 == 0x07"),
        (".vlong 0xF5)", ".vlong 0xF6)"),
        ("owner2 == 0x27 && owner3 == 0x38", "owner2 == 0x28 && owner3 == 0x39"),
        ("regs .br1 == 0x27 && regs .br2 == 0x38", "regs .br1 == 0x28 && regs .br2 == 0x39"),
        (".vlong 0x27)", ".vlong 0x28)"),
        ("rent == 0xFD", "rent == 0xFE"),
        ("regs .br2 == 0xFD", "regs .br2 == 0xFE"),
        ("executable_1_rent_0xFD", "executable_1_rent_0xFE"),
        ("after_skip_key_0x82", "after_skip_key_0x83"),
        ("after_skip_owner2_0x27_owner3_0x38", "after_skip_owner2_0x28_owner3_0x39"),
        ("lamports_18000_dataLen_336", "lamports_19000_dataLen_352"),
        (
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x82)",
            "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x83)",
        ),
    ]
    for old, new in repl:
        text = text.replace(old, new)
    return text


def transform_lean(text: str, *, require_all_terminals: bool = True) -> str:
    text = rename_accounts(text)
    text = bump_knife_and_sem(text)
    text = fix_comments(text)
    text = fix_skip_callee(text)
    text = extend_all_skip_chains(text, require_all=require_all_terminals)
    text = update_test_constants(text)
    return text


def transform_spec(text: str) -> str:
    text = rename_accounts(text)
    text = bump_knife_and_sem(text)
    text = fix_comments(text)
    text = update_test_constants(text)
    return text


def main() -> None:
    skip_only = "--all" not in sys.argv

    lean_lines = SOLANALIB.read_text().splitlines(keepends=True)
    lean_start = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("/-!")
        and i + 1 < len(lean_lines)
        and "knife 128" in lean_lines[i + 1]
    )
    if skip_only:
        lean_end_src = next(
            i for i, line in enumerate(lean_lines)
            if line.startswith("/-!")
            and i + 1 < len(lean_lines)
            and "knife 129" in lean_lines[i + 1]
        )
    else:
        lean_end_src = next(
            i for i, line in enumerate(lean_lines)
            if line.startswith("end ProofForge.Svm.Solanalib")
        )
    lean_file_end = next(
        i for i, line in enumerate(lean_lines)
        if line.startswith("end ProofForge.Svm.Solanalib")
    )
    lean_out = transform_lean(
        "".join(lean_lines[lean_start:lean_end_src]),
        require_all_terminals=not skip_only,
    )
    SOLANALIB.write_text(
        "".join(lean_lines[:lean_file_end]) + lean_out + "end ProofForge.Svm.Solanalib\n"
    )
    print(
        f"Appended Solanalib account-19"
        f"{' skip-only' if skip_only else ''}: {len(lean_out.splitlines())} lines"
    )

    spec_lines = SPEC.read_text().splitlines(keepends=True)
    spec_start = next(
        i for i, line in enumerate(spec_lines)
        if "knife 128" in line.lower() and "account-18" in line
    )
    if skip_only:
        spec_end_src = next(
            i for i, line in enumerate(spec_lines)
            if "knife 129" in line.lower() and "account-18" in line
        )
    else:
        spec_end_src = next(
            i for i, line in enumerate(spec_lines)
            if line.startswith("end Tests.SolanalibSpec")
        )
    end_idx = next(
        i for i, line in enumerate(spec_lines)
        if line.startswith("end Tests.SolanalibSpec")
    )
    spec_out = transform_spec("".join(spec_lines[spec_start:spec_end_src]))
    SPEC.write_text(
        "".join(spec_lines[:end_idx]) + spec_out + "end Tests.SolanalibSpec\n"
    )
    print(
        f"Appended Spec account-19"
        f"{' skip-only' if skip_only else ''}: {len(spec_out.splitlines())} lines"
    )


if __name__ == "__main__":
    main()
