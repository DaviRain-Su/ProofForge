#!/usr/bin/env python3
"""Canonical Borsh and specialized JSON-u128 output scenes against local near-sandbox."""

from __future__ import annotations

import os
import struct
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-output: missing env {name}")
    return value


def _expect(client: NearClient, method: str, args: bytes, expected: bytes) -> None:
    got = client.view(method, args)
    if got != expected:
        raise AssertionError(
            f"{method}({args.hex()}): expected {expected.hex()}, got {got.hex()}"
        )


def _expect_failure(client: NearClient, method: str, args: bytes, scene: str) -> None:
    try:
        client.view(method, args)
    except NearRpcError:
        print(f"near-output: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    unit_wasm = Path(_require("PF_NEAR_UNIT_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearOutput (canonical Borsh + JSON u128) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    _expect(client, "get", b"", NearClient.encode_u64_le(0))
    _expect(client, "emptyBytes", b"", NearClient.borsh_bytes(b""))
    _expect(client, "staticBytes", b"", NearClient.borsh_bytes(b"\x00\x01\xff"))
    _expect(client, "staticString", b"", NearClient.borsh_bytes("😀".encode()))
    expected_values = struct.pack("<IHHH", 3, 1, 513, 65535)
    _expect(client, "staticValues", b"", expected_values)
    print("near-output: empty/bytes/String/UInt16[] exact Borsh bytes ok")

    json_u128 = {
        "jsonU128Zero": 0,
        "jsonU128Two64": 1 << 64,
        "jsonU128Two64PlusOne": (1 << 64) + 1,
        "jsonU128Asymmetric": (1 << 64) + 2,
        "jsonU128Max": (1 << 128) - 1,
    }
    for method, value in json_u128.items():
        expected = f'"{value}"'.encode("ascii")
        _expect(client, method, b"", expected)
        if not (3 <= len(expected) <= 41):
            raise AssertionError(f"{method}: JSON u128 output length escaped 3..41")
    print("near-output: zero/high/mixed/max u128 exact quoted decimal bytes ok")

    for raw in (b"", b"x", bytes(range(8))):
        wire = NearClient.borsh_bytes(raw)
        _expect(client, "echoBytes", wire, wire)
    for text in ("A", "é", "😀"):
        wire = NearClient.borsh_bytes(text.encode())
        _expect(client, "echoString", wire, wire)
    print("near-output: bounded input/output round trips ok")

    _expect(
        client,
        "stringWithByte",
        NearClient.encode_u64_le(ord("A")),
        NearClient.borsh_bytes(b"A"),
    )
    _expect_failure(
        client,
        "stringWithByte",
        NearClient.encode_u64_le(0x80),
        "malformed UTF-8 output",
    )

    _expect(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(0),
        NearClient.borsh_bytes(b""),
    )
    _expect(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(8),
        NearClient.borsh_bytes(bytes(range(1, 9))),
    )
    _expect_failure(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(9),
        "output length above capacity",
    )
    print("near-output: output UTF-8 and capacity guards ok")

    print("=== suite: NearJsonUnitOutput (mutating JSON null) ===")
    client.deploy(unit_wasm)
    # NearOutput and this fixture deliberately share the one-slot `marker` state schema, so the
    # redeployed contract consumes the already initialized zero state instead of reinitializing.
    success = client.call("setMarker", NearClient.encode_u64_le(37))
    returned = NearClient.success_value_bytes(success)
    if returned != b"null":
        raise AssertionError(f"setMarker SuccessValue expected exact b'null', got {returned!r}")
    _expect(client, "get", b"", NearClient.encode_u64_le(37))
    failed = client.call("setMarker", NearClient.encode_u64_le(0), expect_success=False)
    if NearClient.success_value_bytes(failed) is not None:
        raise AssertionError("failed Unit mutation unexpectedly returned a SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(37))
    success = client.call("setMarker", NearClient.encode_u64_le(99))
    if NearClient.success_value_bytes(success) != b"null":
        raise AssertionError("second Unit mutation did not return exact JSON null")
    _expect(client, "get", b"", NearClient.encode_u64_le(99))
    print("near-output: exact null bytes, state persistence, repeated calls, and rollback ok")

    success = client.call("setMarkerVoid", NearClient.encode_u64_le(123))
    if NearClient.success_value_bytes(success) != b"":
        raise AssertionError("void mutation did not return exact empty SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(123))
    failed = client.call("setMarkerVoid", NearClient.encode_u64_le(0), expect_success=False)
    if NearClient.success_value_bytes(failed) is not None:
        raise AssertionError("failed void mutation unexpectedly returned a SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(123))
    success = client.call("setMarkerVoid", NearClient.encode_u64_le(456))
    if NearClient.success_value_bytes(success) != b"":
        raise AssertionError("repeated void mutation did not return exact empty SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(456))
    print("near-output: exact empty return, state persistence, repeated calls, and rollback ok")
    print("suite NearOutput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-output: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
