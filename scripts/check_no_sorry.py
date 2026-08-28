#!/usr/bin/env python3
"""Fail when `sorry` appears as a proof placeholder in Lean sources.

The kernel-proof batch lives inside the `Examples` contracts it talks about.
A `sorry` there would silently downgrade a kernel-checked claim into an
unproved one while CI stays green, so it is gated here instead of trusting
review.

Allowlisted files use `sorry` / `sorryAx` as intentional negative-test
fixtures or as the rejection logic itself:
- `Tests/Fixtures.lean` — `#pf_check` must reject a `sorry`ed def
- `Tests/ProfileSpec.lean` — expects the `axiom sorryAx` rejection message
- `ProofForge/Profile.lean` — owns the `sorryAx` rejection rule
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN_ROOTS = (ROOT / "ProofForge", ROOT / "Examples", ROOT / "Tests")

ALLOWED_FILES = {
    "Tests/Fixtures.lean",
    "Tests/ProfileSpec.lean",
    "ProofForge/Profile.lean",
}

SORRY = re.compile(r"(?<![\w'!?])sorry(?![\w'!?])")
SORRY_AX = re.compile(r"(?<![\w'!?])sorryAx(?![\w'!?])")


def strip_comments(text: str) -> str:
    """Remove Lean block comments (`/- ... -/`, nested) and line comments."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        two = text[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        else:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "--":
                while i < n and text[i] != "\n":
                    i += 1
            else:
                out.append(text[i])
                i += 1
    return "".join(out)


def main() -> int:
    failures: list[str] = []
    for root in SCAN_ROOTS:
        for path in sorted(root.rglob("*.lean")):
            rel = str(path.relative_to(ROOT))
            if rel in ALLOWED_FILES:
                continue
            code = strip_comments(path.read_text(encoding="utf-8"))
            for i, line in enumerate(code.split("\n"), 1):
                if SORRY.search(line):
                    failures.append(f"{rel}:{i}: `sorry` placeholder")
                if SORRY_AX.search(line):
                    failures.append(f"{rel}:{i}: `sorryAx` placeholder")

    for f in failures:
        print(f, file=sys.stderr)
    if failures:
        print(f"check_no_sorry: {len(failures)} violation(s)", file=sys.stderr)
        return 1
    print("check_no_sorry: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())