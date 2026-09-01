#!/usr/bin/env python3
"""Fail when application policy leaks across ProofForge target ownership boundaries.

Also enforces productization P0 (prod-001):
- Examples may use umbrella `import ProofForge` only if listed in the shrink-only allowlist.
- `ProofForge/{Svm,Evm}/Sdk/**` must not import same-target Emit / Assemble / Registry.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "Examples"
TARGET_ROOTS = (
    ROOT / "ProofForge" / "Svm",
    ROOT / "ProofForge" / "Evm",
    ROOT / "ProofForge" / "Wasm",
)
SDK_ROOTS = (
    ROOT / "ProofForge" / "Svm" / "Sdk",
    ROOT / "ProofForge" / "Evm" / "Sdk",
)
# Include the umbrella Sdk.lean files sitting beside the Sdk/ directories.
SDK_FILES_EXTRA = (
    ROOT / "ProofForge" / "Svm" / "Sdk.lean",
    ROOT / "ProofForge" / "Evm" / "Sdk.lean",
)
ALLOWLIST_PATH = ROOT / "scripts" / "umbrella_import_allowlist.txt"

DIRECT_EMIT_IMPORT = re.compile(
    r"^\s*import\s+ProofForge\.(?:Svm|Evm|Wasm)(?:\.[A-Za-z0-9_]+)*\.Emit\s*(?:--.*)?$",
    re.MULTILINE,
)
APPLICATION_IMPORT = re.compile(r"^\s*import\s+(?:Examples|Projects)(?:\.|\s|$)", re.MULTILINE)
PROTOCOL_VOCABULARY = re.compile(
    r"\b(?:Phoenix(?:V1)?|OrderPacket|MarketHeader|TraderState)\b", re.IGNORECASE
)
# Bare umbrella only: `import ProofForge` with no dotted suffix.
UMBRELLA_IMPORT = re.compile(
    r"^\s*import\s+ProofForge\s*(?:--.*)?$",
    re.MULTILINE,
)
# Sdk must not reach compiler/backend surfaces for the same target family.
SDK_FORBIDDEN_IMPORT = re.compile(
    r"^\s*import\s+ProofForge\.(?P<target>Svm|Evm)(?:\.[A-Za-z0-9_]+)*\."
    r"(?P<kind>Emit|Assemble|Registry)(?:\.[A-Za-z0-9_]+)*\s*(?:--.*)?$",
    re.MULTILINE,
)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def report(
    matches: list[str], path: Path, text: str, pattern: re.Pattern[str], message: str
) -> None:
    relative = path.relative_to(ROOT)
    for match in pattern.finditer(text):
        matches.append(
            f"{relative}:{line_number(text, match.start())}: {message}: {match.group(0).strip()}"
        )


def load_allowlist() -> set[str]:
    if not ALLOWLIST_PATH.is_file():
        return set()
    entries: set[str] = set()
    for raw in ALLOWLIST_PATH.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        entries.add(line.replace("\\", "/"))
    return entries


def iter_sdk_files() -> list[Path]:
    files: list[Path] = []
    for root in SDK_ROOTS:
        if root.is_dir():
            files.extend(sorted(root.rglob("*.lean")))
    for path in SDK_FILES_EXTRA:
        if path.is_file():
            files.append(path)
    # Stable unique order
    return sorted(set(files), key=lambda p: str(p))


def main() -> int:
    failures: list[str] = []
    allowlist = load_allowlist()
    umbrella_users: set[str] = set()

    for path in sorted(EXAMPLES.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        report(
            failures,
            path,
            text,
            DIRECT_EMIT_IMPORT,
            "applications must not import target Emit modules directly",
        )
        rel = path.relative_to(ROOT).as_posix()
        if UMBRELLA_IMPORT.search(text):
            umbrella_users.add(rel)
            if rel not in allowlist:
                failures.append(
                    f"{rel}:1: new Examples umbrella import is forbidden "
                    f"(not on shrink-only allowlist {ALLOWLIST_PATH.relative_to(ROOT)}): "
                    f"import ProofForge"
                )

    unknown = sorted(p for p in allowlist if not (ROOT / p).is_file())
    for rel in unknown:
        failures.append(
            f"{rel}: allowlist entry missing on disk; remove it from "
            f"{ALLOWLIST_PATH.relative_to(ROOT)}"
        )

    # Shrink-only: existing allowlist entries that no longer use the umbrella must go.
    stale = sorted(
        rel for rel in (allowlist - umbrella_users) if (ROOT / rel).is_file()
    )
    for rel in stale:
        failures.append(
            f"{rel}: allowlist entry is stale — file no longer has umbrella "
            f"`import ProofForge`; remove it from {ALLOWLIST_PATH.relative_to(ROOT)}"
        )

    for path in iter_sdk_files():
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)
        for match in SDK_FORBIDDEN_IMPORT.finditer(text):
            # Only same-target leakage is in scope for P0 (Svm Sdk → Svm.Emit, etc.).
            target = match.group("target")
            if f"ProofForge/{target}/" in rel.as_posix() or rel.as_posix().startswith(
                f"ProofForge/{target}/"
            ):
                failures.append(
                    f"{rel}:{line_number(text, match.start())}: "
                    f"SDK modules must not import {match.group('kind')}: "
                    f"{match.group(0).strip()}"
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

    print(
        "ownership boundaries: ok "
        f"(umbrella allowlist {len(allowlist)}/{len(umbrella_users)} active)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
