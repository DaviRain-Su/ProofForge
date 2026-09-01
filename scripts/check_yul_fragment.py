#!/usr/bin/env python3
"""Audit ProofForge-emitted Yul against the yul-compiler verified fragment.

Feature B (E-B1) needs a machine-readable reject table before wiring `yulc` as
an alternate backend. This script flags patterns that yul-compiler rejects or
that ProofForge adds outside the upstream opTable surface.

Usage:
  python3 scripts/check_yul_fragment.py path/to/contract.yul
  python3 scripts/check_yul_fragment.py --golden
  python3 scripts/check_yul_fragment.py --self-test

Exit 0 when no *error*-severity findings; warnings do not fail unless --strict.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Strip // and /* */ comments before pattern matching.
BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
LINE_COMMENT = re.compile(r"//[^\n]*")


@dataclass(frozen=True)
class Rule:
    rule_id: str
    severity: str  # error | warn | info
    pattern: re.Pattern[str]
    message: str
    yulc_note: str


RULES: tuple[Rule, ...] = (
    Rule(
        "yulc.gas_builtin",
        "error",
        re.compile(r"(?<![A-Za-z0-9_])gas\s*\(\s*\)"),
        "uses the `gas()` builtin (yul-compiler rejects; needs ExternalsRealized + gas oracle)",
        "README § What is not (yet) done — `gas`",
    ),
    Rule(
        "yulc.linkersymbol",
        "error",
        re.compile(r"linkersymbol\s*\("),
        "contains `linkersymbol(...)` (live symbols need LinkEnv; delegatecall path uses `gas()`)",
        "README § Library linking",
    ),
    Rule(
        "pf.pf_store_addr20",
        "warn",
        re.compile(r"pf_store_addr20\s*\("),
        "ProofForge helper `pf_store_addr20` (not in yul-compiler opTable; inline or lower before yulc)",
        "Emit.lean renderAddr20Helper",
    ),
    Rule(
        "pf.pf_store_fixed_bytes",
        "warn",
        re.compile(r"pf_store_fixed_bytes\s*\("),
        "ProofForge helper `pf_store_fixed_bytes` (not in yul-compiler opTable)",
        "Emit.lean renderFixedBytesHelper",
    ),
    Rule(
        "yulc.memoryguard",
        "info",
        re.compile(r"memoryguard\s*\("),
        "`memoryguard(n)` — yulc spills via desugared scratch contract (msize must not observe reservation)",
        "README § Deep stack access / memoryguard fallback",
    ),
    Rule(
        "yulc.setimmutable",
        "info",
        re.compile(r"setimmutable\s*\("),
        "`setimmutable` — yulc front-end desugars to mstore; source semantics not in theorem",
        "README § Immutables",
    ),
    Rule(
        "yulc.loadimmutable",
        "info",
        re.compile(r"loadimmutable\s*\("),
        "`loadimmutable` — compiles to PUSH32 placeholder; needs ConfMatch.imms at link time",
        "README § Immutables",
    ),
    Rule(
        "pf.nested_object",
        "info",
        re.compile(r"^\s*object\s+", re.MULTILINE),
        "nested `object` tree (supported by yulc object layer; layout must match dataoffset/datasize)",
        "README § object layer",
    ),
    Rule(
        "yulc.selfdestruct",
        "warn",
        re.compile(r"(?<![A-Za-z0-9_])selfdestruct\s*\("),
        "`selfdestruct` — correctness conditional on ExternalsRealized",
        "README § Open-world call/create coverage",
    ),
    Rule(
        "yulc.create",
        "warn",
        re.compile(r"(?<![A-Za-z0-9_])create2?\s*\("),
        "`create`/`create2` — conditional on ExternalsRealized; create path may pass `gas()`",
        "README § Open-world call/create coverage",
    ),
)


@dataclass
class Finding:
    rule: Rule
    line: int
    snippet: str
    program: str | None = None

    def format(self) -> str:
        where = f"{self.program}:" if self.program else ""
        return (
            f"{where}{self.line}: [{self.rule.severity}] {self.rule.rule_id}: "
            f"{self.rule.message} ({self.rule.yulc_note}) — {self.snippet.strip()}"
        )


def strip_comments(text: str) -> str:
    text = BLOCK_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    return LINE_COMMENT.sub("", text)


def scan_yul(text: str, program: str | None = None) -> list[Finding]:
    cleaned = strip_comments(text)
    lines = cleaned.split("\n")
    findings: list[Finding] = []
    for rule in RULES:
        for i, line in enumerate(lines, 1):
            if rule.pattern.search(line):
                findings.append(Finding(rule, i, line, program))
    return findings


def parse_golden_blob(blob: str) -> list[tuple[str, str]]:
    programs: list[tuple[str, str]] = []
    current_name: str | None = None
    current_lines: list[str] = []
    for line in blob.splitlines(keepends=True):
        if line.startswith("--- ") and line.rstrip().endswith(" ---"):
            if current_name is not None:
                programs.append((current_name, "".join(current_lines)))
            current_name = line[4:-4].strip()
            current_lines = []
        elif current_name is not None:
            current_lines.append(line)
    if current_name is not None:
        programs.append((current_name, "".join(current_lines)))
    return programs


def emit_golden_yul() -> str:
    script = ROOT / "scripts" / "emit_evm_golden_yul.lean"
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(script)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "emit_evm_golden_yul.lean failed:\n"
            + (proc.stderr or proc.stdout or "(no output)")
        )
    return proc.stdout


def summarize(findings: list[Finding]) -> dict[str, int]:
    counts: dict[str, int] = {"error": 0, "warn": 0, "info": 0}
    for f in findings:
        counts[f.rule.severity] = counts.get(f.rule.severity, 0) + 1
    return counts


def run_self_test() -> int:
    synthetic = """
    object "T" {
      code {
        let g := gas()
        pf_store_addr20(0, 1, 2, 3)
        call(gas(), 0x1, 0, 0, 0, 0, 0)
        linkersymbol("Lib.sol:Math")
        mstore(64, memoryguard(4096))
        setimmutable(0, "imm0", 1)
        loadimmutable("imm0")
      }
    }
    """
    findings = scan_yul(synthetic, "self-test")
    ids = {f.rule.rule_id for f in findings}
    required = {
        "yulc.gas_builtin",
        "pf.pf_store_addr20",
        "yulc.linkersymbol",
        "yulc.memoryguard",
        "yulc.setimmutable",
        "yulc.loadimmutable",
        "pf.nested_object",
    }
    missing = required - ids
    if missing:
        print(f"check_yul_fragment self-test: missing rules {sorted(missing)}", file=sys.stderr)
        return 1

    try:
        golden = emit_golden_yul()
    except RuntimeError as exc:
        print(f"check_yul_fragment self-test: golden emit failed: {exc}", file=sys.stderr)
        return 1

    programs = parse_golden_blob(golden)
    if not programs:
        print("check_yul_fragment self-test: no golden programs parsed", file=sys.stderr)
        return 1

    names = {name for name, _ in programs}
    for want in ("Counter", "Token"):
        if want not in names:
            print(f"check_yul_fragment self-test: missing golden {want}", file=sys.stderr)
            return 1

    # Counter: memoryguard + pf helpers, no gas() calls.
    counter_yul = next(y for n, y in programs if n == "Counter")
    counter_findings = scan_yul(counter_yul, "Counter")
    counter_ids = {f.rule.rule_id for f in counter_findings}
    if "yulc.gas_builtin" in counter_ids:
        print("check_yul_fragment self-test: Counter should not use gas()", file=sys.stderr)
        return 1
    if "yulc.memoryguard" not in counter_ids:
        print("check_yul_fragment self-test: Counter should use memoryguard", file=sys.stderr)
        return 1

    # Token: external calls pass gas() — must flag yulc.gas_builtin.
    token_yul = next(y for n, y in programs if n == "Token")
    token_findings = scan_yul(token_yul, "Token")
    if not any(f.rule.rule_id == "yulc.gas_builtin" for f in token_findings):
        print("check_yul_fragment self-test: Token should flag gas()", file=sys.stderr)
        return 1

    print("check_yul_fragment: self-test ok")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, help="Yul files to scan")
    parser.add_argument(
        "--golden",
        action="store_true",
        help="emit and scan ProofForge golden programs",
    )
    parser.add_argument("--self-test", action="store_true", help="run built-in checks")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="treat warnings as errors (info still passes)",
    )
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="always exit 0 after printing findings (for inventory runs)",
    )
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()

    all_findings: list[Finding] = []

    if args.golden:
        try:
            blob = emit_golden_yul()
        except RuntimeError as exc:
            print(exc, file=sys.stderr)
            return 1
        for name, yul in parse_golden_blob(blob):
            if yul.lstrip().startswith("// emit error:"):
                print(f"{name}: emit failed ({yul.strip()})", file=sys.stderr)
                return 1
            all_findings.extend(scan_yul(yul, name))

    for path in args.paths:
        if not path.is_file():
            print(f"check_yul_fragment: not a file: {path}", file=sys.stderr)
            return 1
        all_findings.extend(scan_yul(path.read_text(encoding="utf-8"), str(path)))

    if not args.golden and not args.paths:
        parser.print_help()
        return 2

    for finding in all_findings:
        print(finding.format())

    counts = summarize(all_findings)
    print(
        f"check_yul_fragment: {counts['error']} error(s), "
        f"{counts['warn']} warning(s), {counts['info']} info — "
        f"{len(all_findings)} total finding(s)"
    )

    if args.report_only:
        return 0

    fail = counts["error"] > 0 or (args.strict and counts["warn"] > 0)
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
