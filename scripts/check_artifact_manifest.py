#!/usr/bin/env python3
"""Fail when built ProofForge artifacts drift from registry name/digest pins."""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SVM_REGISTRY = ROOT / "ProofForge" / "Svm" / "Registry.lean"
EVM_REGISTRY = ROOT / "ProofForge" / "Evm" / "Registry.lean"

ENTRY_RE = re.compile(
    r'\{\s*name\s*:=\s*"([^"]+)"\s*,\s*digest\s*:=\s*"([0-9a-fA-F]+)"\s*\}'
)
SVM_DIGEST_RE = re.compile(r"^;\s*digest=([0-9a-fA-F]+)\s*$", re.MULTILINE)
EVM_DIGEST_RE = re.compile(r"^//\s*digest=([0-9a-fA-F]+)\s*$", re.MULTILINE)

SVM_SUFFIXES = (".s", ".so", ".idl.json")
EVM_SUFFIXES = (".yul", ".bin", ".abi.json")


def parse_registry(path: Path) -> dict[str, str]:
    text = path.read_text(encoding="utf-8")
    entries = {match.group(1): match.group(2).lower() for match in ENTRY_RE.finditer(text)}
    if not entries:
        raise SystemExit(f"registry/empty: {path.relative_to(ROOT)}")
    return entries


def artifact_stem(path: Path, suffixes: tuple[str, ...]) -> str | None:
    name = path.name
    for suffix in sorted(suffixes, key=len, reverse=True):
        if name.endswith(suffix):
            return name[: -len(suffix)]
    return None


def read_digest(path: Path, pattern: re.Pattern[str]) -> str | None:
    text = path.read_text(encoding="utf-8", errors="replace")
    match = pattern.search(text)
    if match is None:
        return None
    return match.group(1).lower()


def is_elf64(path: Path) -> bool:
    data = path.read_bytes()
    return len(data) >= 5 and data[:4] == b"\x7fELF" and data[4] == 2


def is_even_hex(path: Path) -> bool:
    text = path.read_text(encoding="utf-8").strip()
    if not text or len(text) % 2 != 0:
        return False
    try:
        int(text, 16)
    except ValueError:
        return False
    return True


def check_target(
    *,
    target: str,
    out_dir: Path,
    registry: dict[str, str],
    suffixes: tuple[str, ...],
    digest_path_suffix: str,
    digest_pattern: re.Pattern[str],
    validate_binary,
) -> list[str]:
    failures: list[str] = []
    if not out_dir.is_dir():
        return [f"{target}/missing-out-dir: {out_dir}"]

    present: dict[str, set[str]] = {}
    for path in sorted(out_dir.iterdir()):
        if not path.is_file():
            continue
        stem = artifact_stem(path, suffixes)
        if stem is None:
            failures.append(f"{target}/unexpected-file: {path.name}")
            continue
        present.setdefault(stem, set()).add(path.name[len(stem) :])

    for name in sorted(registry):
        expected = set(suffixes)
        found = present.get(name, set())
        for suffix in sorted(expected - found):
            failures.append(f"{target}/missing: {name}{suffix}")
        for suffix in sorted(found - expected):
            failures.append(f"{target}/extra-suffix: {name}{suffix}")
        if expected <= found:
            source = out_dir / f"{name}{digest_path_suffix}"
            if source.stat().st_size == 0:
                failures.append(f"{target}/empty: {source.name}")
            else:
                digest = read_digest(source, digest_pattern)
                if digest is None:
                    failures.append(f"{target}/digest-missing: {source.name}")
                elif digest != registry[name]:
                    failures.append(
                        f"{target}/digest-mismatch: {name} registry={registry[name]} artifact={digest}"
                    )
            binary = out_dir / f"{name}{'.so' if target == 'svm' else '.bin'}"
            if binary.exists() and binary.stat().st_size == 0:
                failures.append(f"{target}/empty: {binary.name}")
            elif binary.exists() and not validate_binary(binary):
                failures.append(f"{target}/malformed-binary: {binary.name}")

    for name in sorted(set(present) - set(registry)):
        failures.append(f"{target}/orphan: {name}")

    return failures


def check_svm(out_dir: Path, registry: dict[str, str] | None = None) -> list[str]:
    return check_target(
        target="svm",
        out_dir=out_dir,
        registry=registry if registry is not None else parse_registry(SVM_REGISTRY),
        suffixes=SVM_SUFFIXES,
        digest_path_suffix=".s",
        digest_pattern=SVM_DIGEST_RE,
        validate_binary=is_elf64,
    )


def check_evm(out_dir: Path, registry: dict[str, str] | None = None) -> list[str]:
    return check_target(
        target="evm",
        out_dir=out_dir,
        registry=registry if registry is not None else parse_registry(EVM_REGISTRY),
        suffixes=EVM_SUFFIXES,
        digest_path_suffix=".yul",
        digest_pattern=EVM_DIGEST_RE,
        validate_binary=is_even_hex,
    )


def write_svm_fixture(root: Path, name: str, digest: str, *, elf: bool = True) -> None:
    root.mkdir(parents=True, exist_ok=True)
    (root / f"{name}.s").write_text(
        f"; SOLANA-LEAN-SBPF-ASM v0\n; digest={digest}\n.equ NUM_ACCOUNTS, 0x0\n",
        encoding="utf-8",
    )
    (root / f"{name}.idl.json").write_text('{"name":"%s"}' % name, encoding="utf-8")
    so = root / f"{name}.so"
    if elf:
        so.write_bytes(b"\x7fELF\x02" + b"\x00" * 11)
    else:
        so.write_bytes(b"not-elf")


def write_evm_fixture(root: Path, name: str, digest: str, *, hex_ok: bool = True) -> None:
    root.mkdir(parents=True, exist_ok=True)
    (root / f"{name}.yul").write_text(
        f"// PROOF-FORGE-EVM-YUL v0\n// digest={digest}\nobject \"{name}\" {{}}\n",
        encoding="utf-8",
    )
    (root / f"{name}.abi.json").write_text("[]", encoding="utf-8")
    bin_path = root / f"{name}.bin"
    bin_path.write_text("6080" if hex_ok else "608", encoding="utf-8")


def run_self_test() -> int:
    cases: list[tuple[str, bool, list[str]]] = []
    with tempfile.TemporaryDirectory(prefix="pf-artifact-manifest-") as tmp:
        base = Path(tmp)
        svm_reg = {"Alpha": "abc123", "Beta": "def456"}
        evm_reg = {"Gamma": "fedcba", "Delta": "987654"}

        good_svm = base / "good-svm"
        write_svm_fixture(good_svm, "Alpha", "abc123")
        write_svm_fixture(good_svm, "Beta", "def456")
        cases.append(("svm-good", True, check_svm(good_svm, svm_reg)))

        missing = base / "missing-svm"
        write_svm_fixture(missing, "Alpha", "abc123")
        cases.append(("svm-missing", False, check_svm(missing, svm_reg)))

        mismatch = base / "mismatch-svm"
        write_svm_fixture(mismatch, "Alpha", "abc123")
        write_svm_fixture(mismatch, "Beta", "000000")
        cases.append(("svm-digest-mismatch", False, check_svm(mismatch, svm_reg)))

        orphan = base / "orphan-svm"
        write_svm_fixture(orphan, "Alpha", "abc123")
        write_svm_fixture(orphan, "Beta", "def456")
        write_svm_fixture(orphan, "Zeta", "aaaaaa")
        cases.append(("svm-orphan", False, check_svm(orphan, svm_reg)))

        empty = base / "empty-svm"
        empty.mkdir()
        cases.append(("svm-empty-tree", False, check_svm(empty, svm_reg)))

        bad_elf = base / "bad-elf"
        write_svm_fixture(bad_elf, "Alpha", "abc123", elf=False)
        write_svm_fixture(bad_elf, "Beta", "def456")
        cases.append(("svm-bad-elf", False, check_svm(bad_elf, svm_reg)))

        good_evm = base / "good-evm"
        write_evm_fixture(good_evm, "Gamma", "fedcba")
        write_evm_fixture(good_evm, "Delta", "987654")
        cases.append(("evm-good", True, check_evm(good_evm, evm_reg)))

        odd_hex = base / "odd-hex"
        write_evm_fixture(odd_hex, "Gamma", "fedcba", hex_ok=False)
        write_evm_fixture(odd_hex, "Delta", "987654")
        cases.append(("evm-odd-hex", False, check_evm(odd_hex, evm_reg)))

        missing_out = base / "no-such-dir"
        cases.append(("svm-missing-out", False, check_svm(missing_out, svm_reg)))

    failed = 0
    for name, expect_ok, failures in cases:
        ok = len(failures) == 0
        if ok != expect_ok:
            failed += 1
            print(f"self-test/fail: {name} expected_ok={expect_ok} got_failures={failures}", file=sys.stderr)
        else:
            print(f"self-test/ok: {name}")
    if failed:
        print(f"self-test: {failed} case(s) failed", file=sys.stderr)
        return 1
    print("self-test: ok")
    return 0


def report(failures: list[str]) -> int:
    if failures:
        print("artifact manifest violations:", file=sys.stderr)
        for failure in sorted(failures):
            print(f"  {failure}", file=sys.stderr)
        return 1
    print("artifact manifest: ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--target", choices=("svm", "evm", "all"), default="all")
    parser.add_argument("--out", type=Path, help="artifact directory for --target svm|evm")
    parser.add_argument("--svm-out", type=Path, default=ROOT / "build" / "sbpf")
    parser.add_argument("--evm-out", type=Path, default=ROOT / "build" / "evm")
    args = parser.parse_args(argv)

    if args.self_test:
        return run_self_test()

    failures: list[str] = []
    if args.target in ("svm", "all"):
        out = args.out if args.target == "svm" and args.out is not None else args.svm_out
        failures.extend(check_svm(out))
    if args.target in ("evm", "all"):
        out = args.out if args.target == "evm" and args.out is not None else args.evm_out
        failures.extend(check_evm(out))
    return report(failures)


if __name__ == "__main__":
    raise SystemExit(main())
