#!/usr/bin/env python3
"""Regenerate E∞ knives 107-113 (account-15) from account-14 templates (knives 100-106)."""

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

ACC13_SUCCESS_TAIL = (
    "account0NonDupMarker 0x7D 1 1 13000 256 0xF0 0x01 0x22 0x33 1 0xF8"
)
ACC14_SUCCESS_TAIL = (
    "account0NonDupMarker 0x7E 1 1 14000 272 0xF1 0x02 0x23 0x34 1 0xF9"
)
ACC13_ABS_TAIL = "0xBB 0x7D 1 0 13000 256 0xF0 0x01 0x22 0x33 1 0xF8"
ACC14_ABS_TAIL = "0xBB 0x7E 1 0 14000 272 0xF1 0x02 0x23 0x34 1 0xF9"


def rename_accounts(text: str) -> str:
    text = text.replace("account14", "__ACC15__")
    text = text.replace("Account14", "__Acc15__")
    text = text.replace("acc14", "__A15__")
    text = text.replace("key14", "__K15__")
    text = text.replace("account13", "account14")
    text = text.replace("Account13", "Account14")
    text = text.replace("acc13", "acc14")
    text = text.replace("key13", "key14")
    text = text.replace("__ACC15__", "account15")
    text = text.replace("__Acc15__", "Account15")
    text = text.replace("__A15__", "acc15")
    text = text.replace("__K15__", "key15")
    return text


def bump_knife_and_sem(text: str) -> str:
    pairs = [
        ("svm-sem-111", "svm-sem-118"), ("svm-sem-110", "svm-sem-117"),
        ("svm-sem-109", "svm-sem-116"), ("svm-sem-108", "svm-sem-115"),
        ("svm-sem-107", "svm-sem-114"), ("svm-sem-106", "svm-sem-113"),
        ("svm-sem-105", "svm-sem-112"),
        ("knife 106", "knife 113"), ("knife 105", "knife 112"),
        ("knife 104", "knife 111"), ("knife 103", "knife 110"),
        ("knife 102", "knife 109"), ("knife 101", "knife 108"),
        ("knife 100", "knife 107"),
        ("Knife 106", "Knife 113"), ("Knife 105", "Knife 112"),
        ("Knife 104", "Knife 111"), ("Knife 103", "Knife 110"),
        ("Knife 102", "Knife 109"), ("Knife 101", "Knife 108"),
        ("Knife 100", "Knife 107"), ("Knife 99", "Knife 106"),
    ]
    for old, new in pairs:
        text = text.replace(old, new)
    return text


def fix_comments(text: str) -> str:
    text = text.replace("Knife 99 completes account-13 fields", "Knife 106 completes account-14 fields")
    text = text.replace("Knife 106 completes account-13 fields", "Knife 106 completes account-14 fields")
    text = text.replace("from the account-13 header cursor", "from the account-14 header cursor")
    text = text.replace("account-13 zero-dataLen", "account-14 zero-dataLen")
    text = text.replace("plus account-13 zero data_len", "plus account-14 zero data_len")
    text = text.replace("account-13 → account-14", "account-14 → account-15")
    text = text.replace("skip-to-account-14-marker", "skip-to-account-15-marker")
    text = text.replace("quattuordecuple", "quindecuple")
    text = text.replace(
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13",
        "account-0/1/2/3/4/5/6/7/8/9/10/11/12/13/14",
    )
    text = text.replace("account-14 meta", "account-15 meta")
    text = text.replace("account-14 dup", "account-15 dup")
    text = text.replace("account-14 header", "account-15 header")
    text = text.replace("account-14 signer", "account-15 signer")
    text = text.replace("account-14 lamports", "account-15 lamports")
    text = text.replace("account-14 owner", "account-15 owner")
    text = text.replace("account-14 executable", "account-15 executable")
    text = text.replace("account-14 exec", "account-15 exec")
    text = text.replace("account-14 flags", "account-15 flags")
    text = text.replace("account-14 budget", "account-15 budget")
    text = text.replace("for account-14", "for account-15")
    text = text.replace("on account-14", "on account-15")
    text = text.replace("the account-14", "the account-15")
    text = text.replace("account-14,", "account-15,")
    text = text.replace("account-14 ", "account-15 ")
    text = text.replace("account-14.", "account-15.")
    text = text.replace("account-14)", "account-15)")
    text = text.replace("account-14/", "account-15/")
    return text


def fix_skip_callee(text: str) -> str:
    """Skip seeds account-14 via knife-106 exec/rent, then zeroes data_len and stores acc-15 marker."""
    marker = "def account14SkipNextInputMem"
    start = text.find(marker)
    if start == -1:
        return text
    end = text.find("\ndef walkAccount14SkipNextAfterSkipChain?", start)
    if end == -1:
        return text
    block = text[start:end]
    block = block.replace(
        "let m₁ ← account13ExecRentInputMem",
        "let m₁ ← account14ExecRentInputMem",
    )
    old = """      acc14Marker key14Word acc14Signer acc14Writable acc14Lamports acc14DataLen acc14Owner0 acc14Owner1 acc14Owner2 acc14Owner3
      acc14Executable acc14Rent
  let m₂ ← storev .m64 m₁ account14DataLenAddr (.vlong 0)"""
    new = """      acc14Marker key14Word acc14Signer acc14Writable acc14Lamports acc14DataLen acc14Owner0 acc14Owner1 acc14Owner2 acc14Owner3
      acc14Executable acc14Rent
      acc14Marker key14Word acc14Signer acc14Writable acc14Lamports acc14DataLen acc14Owner0 acc14Owner1 acc14Owner2 acc14Owner3
      acc14Executable acc14Rent
  let m₂ ← storev .m64 m₁ account14DataLenAddr (.vlong 0)"""
    block = block.replace(old, new)
    return text[:start] + block + text[end:]


def extend_all_skip_chains(text: str) -> str:
    for term in SKIP_TERMINALS:
        if term in text:
            text = text.replace(term, SKIP_CONT + "\n" + term, 1)
    return text


def update_test_constants(text: str) -> str:
    # Promote predecessor account-13 seeded block → account-14 seeded block in mem calls.
    text = text.replace(ACC13_SUCCESS_TAIL, ACC14_SUCCESS_TAIL)
    text = text.replace(ACC13_ABS_TAIL, ACC14_ABS_TAIL)
    # Replace account-15 target tails; prefix with ACC14 seed so we never corrupt the seed block.
    suffix_repl = [
        # Exec/rent (longest success/abs tails first)
        (
            ACC14_SUCCESS_TAIL
            + " account0NonDupMarker 0x7E 1 1 14000 272 0xF1 0x02 0x23 0x34 1 0xF9",
            ACC14_SUCCESS_TAIL
            + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35 1 0xFA",
        ),
        (
            ACC14_ABS_TAIL + " 0xBC 0x7E 1 0 14000 272 0xF1 0x02 0x23 0x34 1 0xF9",
            ACC14_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35 1 0xFA",
        ),
        # Owner hi
        (
            ACC14_SUCCESS_TAIL
            + " account0NonDupMarker 0x7E 1 1 14000 272 0xF1 0x02 0x23 0x34",
            ACC14_SUCCESS_TAIL
            + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03 0x24 0x35",
        ),
        (
            ACC14_ABS_TAIL + " 0xBC 0x7E 1 0 14000 272 0xF1 0x02 0x23 0x34",
            ACC14_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03 0x24 0x35",
        ),
        # Owner lo
        (
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7E 1 1 14000 272 0xF1 0x02",
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1 15000 288 0xF2 0x03",
        ),
        (
            ACC14_ABS_TAIL + " 0xBC 0x7E 1 0 14000 272 0xF1 0x02",
            ACC14_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288 0xF2 0x03",
        ),
        # Budget
        (
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7E 1 1 14000 272",
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1 15000 288",
        ),
        (
            ACC14_ABS_TAIL + " 0xBC 0x7E 1 0 14000 272",
            ACC14_ABS_TAIL + " 0xBD 0x7F 1 0 15000 288",
        ),
        # Flags
        (
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7E 1 1",
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7F 1 1",
        ),
        (ACC14_ABS_TAIL + " 0xBC 0x7E 1 0", ACC14_ABS_TAIL + " 0xBD 0x7F 1 0"),
        # Meta
        (
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7E\n",
            ACC14_SUCCESS_TAIL + " account0NonDupMarker 0x7F\n",
        ),
        (ACC14_ABS_TAIL + " 0xBC 0x7E", ACC14_ABS_TAIL + " 0xBD 0x7F"),
        # Skip abs marker
        (ACC14_ABS_TAIL + " 0xBC\n", ACC14_ABS_TAIL + " 0xBD\n"),
    ]
    for old, new in suffix_repl:
        text = text.replace(old, new)
    repl = [
        ("regs .br2 == 0x7E", "regs .br2 == 0x7F"),
        ("key == 0x7E", "key == 0x7F"),
        ("dup == 0xBC && key == 0x7F", "dup == 0xBD && key == 0x7F"),
        ("marker == 0xBC", "marker == 0xBD"),
        ("dup == 0xBC", "dup == 0xBD"),
        ("regs .br1 == 14000 && regs .br2 == 272", "regs .br1 == 15000 && regs .br2 == 288"),
        ("lamports == 14000 && dataLen == 272", "lamports == 15000 && dataLen == 288"),
        (".vlong 14000)", ".vlong 15000)"),
        ("owner0 == 0xF1 && owner1 == 0x02", "owner0 == 0xF2 && owner1 == 0x03"),
        ("regs .br1 == 0xF1 && regs .br2 == 0x02", "regs .br1 == 0xF2 && regs .br2 == 0x03"),
        (".vlong 0xF1)", ".vlong 0xF2)"),
        ("owner2 == 0x23 && owner3 == 0x34", "owner2 == 0x24 && owner3 == 0x35"),
        ("regs .br1 == 0x23 && regs .br2 == 0x34", "regs .br1 == 0x24 && regs .br2 == 0x35"),
        (".vlong 0x23)", ".vlong 0x24)"),
        ("rent == 0xF9", "rent == 0xFA"),
        ("regs .br2 == 0xF9", "regs .br2 == 0xFA"),
        ("executable_1_rent_0xF9", "executable_1_rent_0xFA"),
        ("after_skip_key_0x7E", "after_skip_key_0x7F"),
        ("after_skip_owner2_0x23_owner3_0x34", "after_skip_owner2_0x24_owner3_0x35"),
        ("lamports_14000_dataLen_272", "lamports_15000_dataLen_288"),
        ("loadv .m64 finalMem rhsStackAddr == some (.vlong 0x7E)", "loadv .m64 finalMem rhsStackAddr == some (.vlong 0x7F)"),
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


def extract_lines(path: Path, start: int, end: int) -> str:
    lines = path.read_text().splitlines(keepends=True)
    return "".join(lines[start - 1 : end])


def main():
    lean_base = extract_lines(SOLANALIB, 1, 16996)
    lean_src = extract_lines(SOLANALIB, 15491, 16996)
    lean_out = transform_lean(lean_src)
    SOLANALIB.write_text(lean_base + lean_out + "\nend ProofForge.Svm.Solanalib\n")
    print(f"Wrote Solanalib: {len(lean_out.splitlines())} account-15 lines")

    spec_base = extract_lines(SPEC, 1, 2694)
    spec_src = extract_lines(SPEC, 2527, 2694)
    spec_out = transform_spec(spec_src)
    SPEC.write_text(spec_base + "\n" + spec_out + "\nend Tests.SolanalibSpec\n")
    print(f"Wrote Spec: {len(spec_out.splitlines())} account-15 guard lines")


if __name__ == "__main__":
    main()
