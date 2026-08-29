#!/usr/bin/env python3
"""Canonical Borsh bounded bytes/string scenes against local near-sandbox."""

from __future__ import annotations

import os
import struct
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-bytes: missing env {name}")
    return value


def _expect_view_failure(client: NearClient, method: str, args: bytes, scene: str) -> None:
    try:
        client.view(method, args)
    except NearRpcError:
        print(f"near-bytes: {scene} rejected ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def _expect_u64(client: NearClient, method: str, args: bytes, expected: int) -> None:
    got = client.view_u64(method, args)
    if got != expected:
        raise AssertionError(f"{method}({args.hex()}): expected {expected}, got {got}")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearBytes (canonical Borsh bytes / strict UTF-8) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    _expect_u64(client, "inspectBytes", NearClient.borsh_bytes(b""), 0)
    _expect_u64(client, "inspectBytes", NearClient.borsh_bytes(b"\x0b"), 12)
    _expect_u64(client, "inspectBytes", NearClient.borsh_bytes(bytes(range(1, 9))), 17)
    print("near-bytes: lengths 0/1/8 and inactive-slot zeroing ok")

    malformed_bytes = (
        (b"\x00\x00\x00", "short u32 length"),
        (struct.pack("<I", 2) + b"x", "declared length exceeds payload"),
        (struct.pack("<I", 1) + b"xy", "trailing byte"),
        (NearClient.borsh_bytes(b"123456789"), "capacity overflow"),
    )
    for wire, scene in malformed_bytes:
        _expect_view_failure(client, "inspectBytes", wire, scene)

    valid_strings = (
        ("A", 66),
        ("é", 197),
        ("€", 229),
        ("😀", 244),
        ("abcdefgh", 209),
    )
    for text, expected in valid_strings:
        _expect_u64(client, "inspectString", NearClient.borsh_bytes(text.encode()), expected)
    print("near-bytes: ASCII and valid 2/3/4-byte Unicode scalar UTF-8 accepted ok")

    invalid_utf8 = (
        (b"\xc0\xaf", "overlong two-byte sequence"),
        (b"\xed\xa0\x80", "UTF-16 surrogate"),
        (b"\xe2\x82", "truncated three-byte sequence"),
        (b"\x80", "stray continuation"),
        (b"\xf4\x90\x80\x80", "code point above U+10FFFF"),
    )
    for raw, scene in invalid_utf8:
        wire = NearClient.borsh_bytes(raw)
        _expect_view_failure(client, "inspectString", wire, scene)
        _expect_u64(client, "inspectBytes", wire, len(raw) + raw[0])
    print("near-bytes: malformed UTF-8 rejected as String but retained as bytes ok")
    print("suite NearBytes: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-bytes: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
