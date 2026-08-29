#!/usr/bin/env python3
"""Fail when application policy leaks across ProofForge target ownership boundaries."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "Examples"
TARGET_ROOTS = (ROOT / "ProofForge" / "Svm", ROOT / "ProofForge" / "Evm",
                ROOT / "ProofForge" / "Wasm")

DIRECT_EMIT_IMPORT = re.compile(
    r"^\s*import\s+ProofForge\.(?:Svm|Evm|Wasm)(?:\.[A-Za-z0-9_]+)*\.Emit\s*(?:--.*)?$",
    re.MULTILINE,
)
APPLICATION_IMPORT = re.compile(r"^\s*import\s+(?:Examples|Projects)(?:\.|\s|$)", re.MULTILINE)
PROTOCOL_VOCABULARY = re.compile(
    r"\b(?:Phoenix(?:V1)?|OrderPacket|MarketHeader|TraderState)\b", re.IGNORECASE
)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def report(matches: list[str], path: Path, text: str, pattern: re.Pattern[str], message: str) -> None:
    relative = path.relative_to(ROOT)
    for match in pattern.finditer(text):
        matches.append(f"{relative}:{line_number(text, match.start())}: {message}: {match.group(0).strip()}")


def main() -> int:
    failures: list[str] = []

    for path in sorted(EXAMPLES.rglob("*.lean")):
        report(
            failures,
            path,
            path.read_text(encoding="utf-8"),
            DIRECT_EMIT_IMPORT,
            "applications must not import target Emit modules directly",
        )

    target_paths = [path for target_root in TARGET_ROOTS for path in target_root.rglob("*.lean")]
    for path in sorted(target_paths):
        if path.name == "Registry.lean":
            continue
        text = path.read_text(encoding="utf-8")
        report(
            failures,
            path,
            text,
            APPLICATION_IMPORT,
            "target-owned modules must not import application modules",
        )
        report(
            failures,
            path,
            text,
            PROTOCOL_VOCABULARY,
            "protocol vocabulary belongs in Examples, not generic target modules",
        )

    if failures:
        print("ownership boundary violations:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("ownership boundaries: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
