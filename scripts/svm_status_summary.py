#!/usr/bin/env python3
"""Summarize SVM plan task front-matter statuses (svm-eng-002).

Reads docs/plan/tasks/{sf,svm}-*.md and prints a compact board. Exit 0 always
unless a task file is missing required front-matter keys.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TASKS = ROOT / "docs" / "plan" / "tasks"

FRONT = re.compile(
    r"^---\s*\n(.*?)\n---",
    re.DOTALL | re.MULTILINE,
)


def parse_front(text: str) -> dict[str, str]:
    m = FRONT.match(text)
    if not m:
        return {}
    out: dict[str, str] = {}
    for line in m.group(1).splitlines():
        if ":" not in line:
            continue
        key, value = line.split(":", 1)
        out[key.strip()] = value.strip().strip("[]")
    return out


def main() -> int:
    rows: list[tuple[str, str, str]] = []
    errors: list[str] = []
    for path in sorted(TASKS.glob("sf-*.md")) + sorted(TASKS.glob("svm-*.md")):
        meta = parse_front(path.read_text(encoding="utf-8"))
        tid = meta.get("id") or path.stem
        status = meta.get("status")
        if status is None:
            errors.append(f"{path}: missing status")
            continue
        track = meta.get("track", "?")
        rows.append((track, tid, status))

    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        return 1

    counts: dict[str, int] = {}
    for _, _, status in rows:
        counts[status] = counts.get(status, 0) + 1

    print("SVM plan status summary")
    print("=======================")
    for status in ("done", "doing", "todo", "n/a"):
        if status in counts:
            print(f"  {status:6} {counts[status]}")
    extras = sorted(set(counts) - {"done", "doing", "todo", "n/a"})
    for status in extras:
        print(f"  {status:6} {counts[status]}")
    print()
    print(f"{'track':12} {'id':16} status")
    print("-" * 40)
    for track, tid, status in rows:
        print(f"{track:12} {tid:16} {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
