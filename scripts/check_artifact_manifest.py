#!/usr/bin/env python3
"""Fail when build artifacts drift from target registry names, kinds, or digests."""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

ENTRY_RE = re.compile(
    r'\{\s*name\s*:=\s*"([^"]+)"\s*,\s*digest\s*:=\s*"([^"]+)"\s*\}'
)
HEX_RE = re.compile(r"^[0-9a-f]+$")
DIGEST_LINE = {
    "svm": re.compile(r"^;\s*digest=([0-9a-f]+)\s*$"),
    "evm": re.compile(r"^//\s*digest=([0-9a-f]+)\s*$"),
    "xrpl": re.compile(r"^;;\s*digest=([0-9a-f]+)\s*$"),
    "near": re.compile(r"^;;\s*digest=([0-9a-f]+)\s*$"),
}

# `.so` must win over `.s`; `Name.so`.endswith(".s") is true.
SUFFIXES_BY_SPECIFICITY = (".idl.json", ".abi.json", ".so", ".bin", ".yul", ".wasm", ".wat", ".rs", ".s")


@dataclass(frozen=True)
class TargetSpec:
    key: str
    registry_rel: Path
    expected_count: int
    suffixes: tuple[str, ...]
    digest_suffix: str


SVM = TargetSpec(
    key="svm",
    registry_rel=Path("ProofForge/Svm/Registry.lean"),
    expected_count=70,
    suffixes=(".so", ".s", ".idl.json"),
    digest_suffix=".s",
)
EVM = TargetSpec(
    key="evm",
    registry_rel=Path("ProofForge/Evm/Registry.lean"),
    expected_count=44,
    suffixes=(".bin", ".yul", ".abi.json"),
    digest_suffix=".yul",
)
XRPL = TargetSpec(
    key="xrpl",
    registry_rel=Path("ProofForge/Wasm/Xrpl/Registry.lean"),
    expected_count=23,
    suffixes=(".wasm", ".wat"),
    digest_suffix=".wat",
)
NEAR = TargetSpec(
    key="near",
    registry_rel=Path("ProofForge/Wasm/Near/Registry.lean"),
    expected_count=32,
    suffixes=(".wasm", ".wat"),
    digest_suffix=".wat",
)
SPECS = {"svm": SVM, "evm": EVM, "xrpl": XRPL, "near": NEAR}
ELF_MAGIC = b"\x7fELF"
ELF64_CLASS = 2
ELF64_DATA_LSB = 1
ELF64_VERSION = 1
ELF_ET_DYN = 3
ELF_EM_SBPF = 247
ELF64_EHDR_SIZE = 64


def artifact_suffix(filename: str) -> str | None:
    for suffix in SUFFIXES_BY_SPECIFICITY:
        if filename.endswith(suffix):
            return suffix
    return None


def parse_registry(path: Path) -> dict[str, str]:
    text = path.read_text(encoding="utf-8")
    entries: dict[str, str] = {}
    for name, digest in ENTRY_RE.findall(text):
        if name in entries:
            raise ValueError(f"duplicate registry name: {name}")
        if not HEX_RE.fullmatch(digest):
            raise ValueError(f"malformed registry digest: {name}")
        entries[name] = digest
    return entries


def load_entries(root: Path, spec: TargetSpec, *, pin_count: bool) -> tuple[dict[str, str], list[str]]:
    path = root / spec.registry_rel
    diags: list[str] = []
    if not path.is_file():
        return {}, [f"missing registry: {spec.registry_rel}"]
    try:
        entries = parse_registry(path)
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        return {}, [f"malformed registry: {spec.registry_rel}: {exc}"]
    if pin_count and len(entries) != spec.expected_count:
        diags.append(
            f"registry count: {spec.key} expected={spec.expected_count} found={len(entries)}"
        )
    return entries, diags


def rel_to(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def iter_artifacts(out_dir: Path) -> list[tuple[Path, str, str]]:
    found: list[tuple[Path, str, str]] = []
    for path in out_dir.rglob("*"):
        if not path.is_file():
            continue
        suffix = artifact_suffix(path.name)
        if suffix is None:
            continue
        found.append((path, path.name[: -len(suffix)], suffix))
    return found


def read_digest(path: Path, spec: TargetSpec) -> str | None:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    pattern = DIGEST_LINE[spec.key]
    for line in text.splitlines():
        match = pattern.match(line)
        if match:
            return match.group(1)
    return None


def check_json(path: Path, rel: str, diags: list[str]) -> None:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        diags.append(f"malformed file: {rel}: not text")
        return
    try:
        json.loads(text)
    except json.JSONDecodeError:
        diags.append(f"malformed file: {rel}: invalid json")


def check_elf64(path: Path, rel: str, diags: list[str]) -> None:
    try:
        header = path.read_bytes()[:ELF64_EHDR_SIZE]
    except OSError:
        diags.append(f"malformed file: {rel}: unreadable")
        return
    if len(header) < ELF64_EHDR_SIZE:
        diags.append(f"not elf64: {rel}: truncated header")
        return
    if header[:4] != ELF_MAGIC or header[4] != ELF64_CLASS:
        diags.append(f"not elf64: {rel}")
        return
    if header[5] != ELF64_DATA_LSB or header[6] != ELF64_VERSION:
        diags.append(f"not elf64: {rel}: bad ident")
        return
    e_type = int.from_bytes(header[16:18], "little")
    e_machine = int.from_bytes(header[18:20], "little")
    e_version = int.from_bytes(header[20:24], "little")
    e_ehsize = int.from_bytes(header[52:54], "little")
    if e_type != ELF_ET_DYN or e_machine != ELF_EM_SBPF:
        diags.append(f"not sbpf elf: {rel}: type={e_type} machine={e_machine}")
        return
    if e_version != ELF64_VERSION or e_ehsize != ELF64_EHDR_SIZE:
        diags.append(f"not elf64: {rel}: bad version/ehsize")


def check_wasm(path: Path, rel: str, diags: list[str]) -> None:
    try:
        header = path.read_bytes()[:4]
    except OSError:
        diags.append(f"malformed file: {rel}: unreadable")
        return
    if header != b"\x00asm":
        diags.append(f"not wasm: {rel}")


def check_bin_hex(path: Path, rel: str, diags: list[str]) -> None:
    try:
        text = path.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeDecodeError):
        diags.append(f"malformed file: {rel}: not text")
        return
    if text == "":
        diags.append(f"malformed file: {rel}: empty hex")
        return
    # Assembler emits raw even-length hex only. Reject int()-accepted forms like 0x / +/-.
    if not re.fullmatch(r"[0-9a-fA-F]+", text):
        diags.append(f"malformed file: {rel}: not hex")
        return
    if len(text) % 2 != 0:
        diags.append(f"malformed file: {rel}: odd-length hex")


def check_expected_file(path: Path, spec: TargetSpec, suffix: str, diags: list[str], out_dir: Path) -> None:
    rel = rel_to(path, out_dir)
    if path.stat().st_size == 0:
        diags.append(f"empty file: {rel}")
        return
    if suffix == spec.digest_suffix:
        digest = read_digest(path, spec)
        if digest is None:
            diags.append(f"malformed file: {rel}: missing digest")
    elif suffix in {".idl.json", ".abi.json"}:
        check_json(path, rel, diags)
    elif suffix == ".so":
        check_elf64(path, rel, diags)
    elif suffix == ".bin":
        check_bin_hex(path, rel, diags)
    elif suffix == ".wasm":
        check_wasm(path, rel, diags)


def check_target(
    spec: TargetSpec,
    entries: dict[str, str],
    out_dir: Path,
) -> list[str]:
    diags: list[str] = []
    if not out_dir.is_dir():
        return [f"missing out dir: {out_dir}"]

    other_suffixes = set()
    for other in SPECS.values():
        if other.key != spec.key:
            other_suffixes.update(other.suffixes)

    owned_stems: set[str] = set()
    for path, stem, suffix in iter_artifacts(out_dir):
        rel = rel_to(path, out_dir)
        if suffix in other_suffixes and suffix not in spec.suffixes:
            diags.append(f"unexpected kind: {rel}")
            continue
        if suffix not in spec.suffixes:
            continue
        owned_stems.add(stem)

    for stem in sorted(owned_stems - set(entries)):
        diags.append(f"orphan stem: {spec.key} {stem}")

    for name in sorted(entries):
        for suffix in spec.suffixes:
            path = out_dir / f"{name}{suffix}"
            if not path.is_file():
                diags.append(f"missing artifact: {spec.key} {name}{suffix}")
                continue
            check_expected_file(path, spec, suffix, diags, out_dir)
        digest_path = out_dir / f"{name}{spec.digest_suffix}"
        if digest_path.is_file() and digest_path.stat().st_size > 0:
            found = read_digest(digest_path, spec)
            expected = entries[name]
            if found is not None and found != expected:
                diags.append(
                    f"digest mismatch: {spec.key} {name} registry={expected} artifact={found}"
                )

    return diags


def diagnostics(
    target: str,
    out_dir: Path,
    *,
    root: Path = ROOT,
    entries_by_target: dict[str, dict[str, str]] | None = None,
    pin_count: bool = True,
) -> list[str]:
    if target == "all":
        specs = [SVM, EVM, XRPL, NEAR]
    else:
        specs = [SPECS[target]]
    diags: list[str] = []
    loaded: list[tuple[TargetSpec, dict[str, str]]] = []
    for spec in specs:
        if entries_by_target is not None:
            entries = entries_by_target[spec.key]
            load_diags: list[str] = []
        else:
            entries, load_diags = load_entries(root, spec, pin_count=pin_count)
        diags.extend(load_diags)
        loaded.append((spec, entries))
        if not entries and entries_by_target is None and not load_diags:
            diags.append(f"empty registry: {spec.key}")
    for spec, entries in loaded:
        if entries or entries_by_target is not None:
            target_out_dir = out_dir / spec.key if target == "all" else out_dir
            diags.extend(
                check_target(
                    spec,
                    entries,
                    target_out_dir,
                )
            )
    return sorted(set(diags))


def report(diags: list[str]) -> int:
    if diags:
        print("artifact manifest errors:", file=sys.stderr)
        for item in diags:
            print(f"  {item}", file=sys.stderr)
        return 1
    print("artifact manifest: ok")
    return 0


def make_sbpf_elf_header(
    *,
    ei_class: int = ELF64_CLASS,
    ei_data: int = ELF64_DATA_LSB,
    ei_version: int = ELF64_VERSION,
    e_type: int = ELF_ET_DYN,
    e_machine: int = ELF_EM_SBPF,
    e_version: int = ELF64_VERSION,
    e_ehsize: int = ELF64_EHDR_SIZE,
) -> bytes:
    header = bytearray(ELF64_EHDR_SIZE)
    header[0:4] = ELF_MAGIC
    header[4] = ei_class
    header[5] = ei_data
    header[6] = ei_version
    header[16:18] = e_type.to_bytes(2, "little")
    header[18:20] = e_machine.to_bytes(2, "little")
    header[20:24] = e_version.to_bytes(4, "little")
    header[52:54] = e_ehsize.to_bytes(2, "little")
    return bytes(header)


ELF64_STUB = make_sbpf_elf_header()


def _write_registry(path: Path, entries: list[tuple[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    body = ",\n".join(f'  {{ name := "{name}", digest := "{digest}" }}' for name, digest in entries)
    path.write_text(f"def entries : Array Entry := #[\n{body}\n]\n", encoding="utf-8")


def _write_svm(out: Path, name: str, digest: str, *, so: bytes | None = ELF64_STUB) -> None:
    out.mkdir(parents=True, exist_ok=True)
    if so is not None:
        (out / f"{name}.so").write_bytes(so)
    (out / f"{name}.s").write_text(f"; digest={digest}\n", encoding="utf-8")
    (out / f"{name}.idl.json").write_text("{}\n", encoding="utf-8")


def _write_evm(out: Path, name: str, digest: str, *, bin_hex: str = "deadbeef") -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{name}.bin").write_text(f"{bin_hex}\n", encoding="utf-8")
    (out / f"{name}.yul").write_text(f"// digest={digest}\n", encoding="utf-8")
    (out / f"{name}.abi.json").write_text("[]\n", encoding="utf-8")


def _write_xrpl(out: Path, name: str, digest: str, *, wasm: bytes | None = b"\x00asm") -> None:
    out.mkdir(parents=True, exist_ok=True)
    if wasm is not None:
        (out / f"{name}.wasm").write_bytes(wasm)
    (out / f"{name}.wat").write_text(
        f";; PROOF-FORGE-XRPL-BEDROCK v0\n;; digest={digest}\n(module)\n", encoding="utf-8"
    )


def _write_near(out: Path, name: str, digest: str, *, wasm: bytes | None = b"\x00asm") -> None:
    out.mkdir(parents=True, exist_ok=True)
    if wasm is not None:
        (out / f"{name}.wasm").write_bytes(wasm)
    (out / f"{name}.wat").write_text(
        f";; PROOF-FORGE-NEAR-RAW-U64 v0\n;; digest={digest}\n(module)\n", encoding="utf-8"
    )


def _require(diags: list[str], needle: str, label: str) -> None:
    if not any(needle in item for item in diags):
        raise AssertionError(f"{label}: expected {needle!r} in {diags}")


def self_test() -> int:
    failures: list[str] = []
    ran = 0

    def case(name: str, fn: Callable[[], None]) -> None:
        nonlocal ran
        ran += 1
        try:
            fn()
        except AssertionError as exc:
            failures.append(f"{name}: {exc}")

    svm_entries = {"Prog": "abc123"}
    evm_entries = {"Tok": "def456"}
    xrpl_entries = {"Counter": "fed789"}
    near_entries = {"Counter": "ba9876"}
    injected = {"svm": svm_entries, "evm": evm_entries, "xrpl": xrpl_entries, "near": near_entries}

    def parse_real() -> None:
        svm = parse_registry(ROOT / SVM.registry_rel)
        evm = parse_registry(ROOT / EVM.registry_rel)
        xrpl = parse_registry(ROOT / XRPL.registry_rel)
        near = parse_registry(ROOT / NEAR.registry_rel)
        if len(svm) != SVM.expected_count:
            raise AssertionError(f"svm count {len(svm)}")
        if len(evm) != EVM.expected_count:
            raise AssertionError(f"evm count {len(evm)}")
        if len(xrpl) != XRPL.expected_count:
            raise AssertionError(f"xrpl count {len(xrpl)}")
        if len(near) != NEAR.expected_count:
            raise AssertionError(f"near count {len(near)}")
        if svm["Counter"] != "3382e308fa0843e9":
            raise AssertionError("svm Counter digest")
        if evm["Counter"] != "254202356ee921d6":
            raise AssertionError("evm Counter digest")
        if xrpl["Counter"] != "e029f72296e320be":
            raise AssertionError("xrpl Counter digest")
        if near["Counter"] != "121a0c8f7e697642":
            raise AssertionError("near Counter digest")

    def happy() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out / "svm", "Prog", "abc123")
            _write_evm(out / "evm", "Tok", "def456")
            _write_xrpl(out / "xrpl", "Counter", "fed789")
            _write_near(out / "near", "Counter", "ba9876")
            diags = diagnostics("all", out, entries_by_target=injected, pin_count=False)
            if diags:
                raise AssertionError(diags)

    def missing_so() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "abc123", so=None)
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "missing artifact: svm Prog.so", "missing_so")

    def digest_mismatch() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "000111")
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "digest mismatch: svm Prog", "digest_mismatch")

    def orphan() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "abc123")
            _write_svm(out, "Extra", "abc123")
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "orphan stem: svm Extra", "orphan")

    def empty_tree() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "missing artifact: svm Prog.so", "empty_tree")

    def bad_elf() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "abc123", so=ELF_MAGIC + bytes([1]) + bytes(11))
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "not elf64:", "bad_elf")

    def truncated_elf() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            # Old gate accepted magic+class alone. Truncated headers must fail.
            _write_svm(out, "Prog", "abc123", so=ELF_MAGIC + bytes([ELF64_CLASS]) + bytes(11))
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "truncated header", "truncated_elf")

    def bad_machine() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "abc123", so=make_sbpf_elf_header(e_machine=62))
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "not sbpf elf:", "bad_machine")

    def odd_hex() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_evm(out, "Tok", "def456", bin_hex="deadbee")
            diags = diagnostics("evm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "odd-length hex", "odd_hex")

    def prefixed_hex() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_evm(out, "Tok", "def456", bin_hex="0x6080")
            diags = diagnostics("evm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "not hex", "prefixed_hex")

    def signed_hex() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_evm(out, "Tok", "def456", bin_hex="+6080")
            diags = diagnostics("evm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "not hex", "signed_hex")

    def unexpected_kind() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            _write_svm(out, "Prog", "abc123")
            (out / "Prog.bin").write_text("aa\n", encoding="utf-8")
            diags = diagnostics("svm", out, entries_by_target=injected, pin_count=False)
            if not diags:
                raise AssertionError("expected failure")
            _require(diags, "unexpected kind: Prog.bin", "unexpected_kind")

    def synthetic_registry() -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_registry(root / SVM.registry_rel, [("Prog", "abc123")])
            _write_registry(root / EVM.registry_rel, [("Tok", "def456")])
            out = root / "out"
            _write_svm(out, "Prog", "abc123")
            loaded, load_diags = load_entries(root, SVM, pin_count=False)
            if load_diags or loaded != {"Prog": "abc123"}:
                raise AssertionError((loaded, load_diags))
            diags = diagnostics("svm", out, root=root, pin_count=False)
            if diags:
                raise AssertionError(diags)

    case("parse_real", parse_real)
    case("happy", happy)
    case("missing_so", missing_so)
    case("digest_mismatch", digest_mismatch)
    case("orphan", orphan)
    case("empty_tree", empty_tree)
    case("bad_elf", bad_elf)
    case("truncated_elf", truncated_elf)
    case("bad_machine", bad_machine)
    case("odd_hex", odd_hex)
    case("prefixed_hex", prefixed_hex)
    case("signed_hex", signed_hex)
    case("unexpected_kind", unexpected_kind)
    case("synthetic_registry", synthetic_registry)

    if failures:
        print("artifact manifest self-test failures:", file=sys.stderr)
        for item in failures:
            print(f"  {item}", file=sys.stderr)
        return 1
    print(f"artifact manifest self-test: {ran} passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--target", choices=("svm", "evm", "xrpl", "near", "all"))
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.self_test:
        if args.target is not None or args.out is not None:
            print("usage: check_artifact_manifest.py --self-test", file=sys.stderr)
            return 2
        return self_test()
    if args.target is None or args.out is None:
        print(
            "usage: check_artifact_manifest.py --target svm|evm|xrpl|near|all --out DIR",
            file=sys.stderr,
        )
        return 2
    return report(diagnostics(args.target, args.out))


if __name__ == "__main__":
    raise SystemExit(main())
