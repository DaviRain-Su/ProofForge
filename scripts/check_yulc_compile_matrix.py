#!/usr/bin/env python3
"""Report which EVM registry programs yulc accepts (compile matrix for E-B1/E-B3).

Requires: ./scripts/build_yulc.sh, lake exe pf.

Usage:
  python3 scripts/check_yulc_compile_matrix.py
  python3 scripts/check_yulc_compile_matrix.py --programs Counter,Capped,Token
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
YULC = ROOT / "powdr-probe/.lake/packages/yul_evm_compiler/.lake/build/bin/yulc"

DEFAULT_PROGRAMS = [
    "Counter",
    "Capped",
    "Const",
    "Wide",
    "Flag",
    "Phase",
    "Ownable",
    "Token",
    "TipJar",
    "Vault",
]


def yulc_build(program: str, out: Path) -> tuple[str, str]:
    env = os.environ.copy()
    if YULC.is_file():
        env["PROOFFORGE_YULC"] = str(YULC)
    proc = subprocess.run(
        ["lake", "exe", "pf", "--", "build", "--target", "evm",
         "--out", str(out), "--backend", "yulc", program],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        bin_path = out / f"{program}.bin"
        if bin_path.is_file():
            hex_len = len(bin_path.read_text().strip())
            return "accept", f"{hex_len} hex chars"
        return "accept", "no .bin"
    err = proc.stderr + proc.stdout
    if "yulc rejected" in err or "unsupported compiler features" in err:
        return "reject", "fragment"
    if "gas()" in err or "assemble/tool" in err:
        return "reject", err.strip().split("\n")[-1][:80]
    return "error", err.strip().split("\n")[-1][:80]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--programs", default=",".join(DEFAULT_PROGRAMS))
    args = parser.parse_args()
    programs = [p.strip() for p in args.programs.split(",") if p.strip()]

    if not YULC.is_file():
        print("check_yulc_compile_matrix: skip (yulc not built; run ./scripts/build_yulc.sh)", file=sys.stderr)
        return 0

    print(f"{'program':<12} {'yulc':<8} detail")
    print("-" * 60)
    accepts = 0
    for program in programs:
        with tempfile.TemporaryDirectory(prefix="yulc-matrix-") as tmp:
            status, detail = yulc_build(program, Path(tmp))
        if status == "accept":
            accepts += 1
        print(f"{program:<12} {status:<8} {detail}")

    print(f"\ncheck_yulc_compile_matrix: {accepts}/{len(programs)} accepted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
