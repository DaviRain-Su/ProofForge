#!/usr/bin/env python3
"""Assert ProofForge.{Svm,Evm}.Sdk transitive imports never reach Emit/Assemble/Registry.

Walks Lean `import` edges under the repo (ProofForge/** only). Used by CI for prod-002.
"""

from __future__ import annotations

import re
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PF = ROOT / "ProofForge"

IMPORT_RE = re.compile(r"^\s*import\s+(ProofForge(?:\.[A-Za-z0-9_]+)+)\s*(?:--.*)?$", re.M)
FORBIDDEN_SUFFIXES = (".Emit", ".Assemble", ".Registry")

ENTRYPOINTS = (
    "ProofForge.Svm.Sdk",
    "ProofForge.Evm.Sdk",
)


def module_to_path(mod: str) -> Path | None:
    parts = mod.split(".")
    if parts[0] != "ProofForge":
        return None
    rel = Path(*parts[1:])
    candidates = [PF / rel.with_suffix(".lean"), PF / rel / "Sdk.lean"]
    # ProofForge.Svm.Sdk → ProofForge/Svm/Sdk.lean
    direct = PF.joinpath(*parts[1:]).with_suffix(".lean")
    if direct.is_file():
        return direct
    return None


def imports_of(mod: str) -> list[str]:
    path = module_to_path(mod)
    if path is None or not path.is_file():
        return []
    text = path.read_text(encoding="utf-8")
    return [m.group(1) for m in IMPORT_RE.finditer(text)]


def is_forbidden(mod: str) -> bool:
    # Same-target backend surfaces only (Svm/Evm).
    for target in ("Svm", "Evm"):
        prefix = f"ProofForge.{target}."
        if not mod.startswith(prefix):
            continue
        rest = mod[len(prefix) :]
        head = rest.split(".", 1)[0]
        if head in ("Emit", "Assemble", "Registry"):
            return True
        # Nested: ProofForge.Svm.AccountStorage.Emit
        if any(part in ("Emit", "Assemble", "Registry") for part in rest.split(".")):
            return True
    return False


def closure(entry: str) -> tuple[set[str], list[str]]:
    seen: set[str] = set()
    bad: list[str] = []
    q: deque[str] = deque([entry])
    while q:
        mod = q.popleft()
        if mod in seen:
            continue
        seen.add(mod)
        if is_forbidden(mod):
            bad.append(mod)
            continue
        for dep in imports_of(mod):
            if dep not in seen:
                q.append(dep)
    return seen, bad


def main() -> int:
    failures: list[str] = []
    for entry in ENTRYPOINTS:
        path = module_to_path(entry)
        if path is None:
            failures.append(f"missing entry module file for {entry}")
            continue
        seen, bad = closure(entry)
        if bad:
            for mod in sorted(set(bad)):
                failures.append(f"{entry} transitively imports forbidden {mod}")
        print(f"{entry}: closure {len(seen)} modules, forbidden={len(bad)}")
    if failures:
        print("sdk import-closure violations:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print("sdk import-closure: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
