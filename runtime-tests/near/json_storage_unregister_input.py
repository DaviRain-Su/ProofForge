#!/usr/bin/env python3
"""Bounded storage-unregister-shaped JSON argument scenes against near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-storage-unregister-input: missing env {name}")
    return value


def _expect(client: NearClient, wire: bytes, expected: int) -> None:
    got = client.view("inspectForce", wire)
    encoded = NearClient.encode_u64_le(expected)
    if got != encoded:
        raise AssertionError(f"expected {encoded.hex()}, got {got.hex()} for {wire!r}")


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("inspectForce", wire)
    except NearRpcError:
        print(f"near-json-storage-unregister-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonStorageUnregisterInput (optional force) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(9))

    for wire in (b"{}", b'{"force":null}', b' { "force" : null } '):
        _expect(client, wire, 0)
    _expect(client, b'{"force":false}', 1)
    _expect(client, b'{"force":true}', 2)

    max_wire = b" " * 32 + b'{"force":false}'
    if len(max_wire) != 47:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 47")
    _expect(client, max_wire, 1)

    result = client.call("commitForce", b'{"force":true}')
    returned = NearClient.success_value_bytes(result)
    if returned != NearClient.encode_u64_le(2):
        raise AssertionError(f"mutating parser returned wrong discriminant: {returned!r}")
    if client.view_u64("get") != 2:
        raise AssertionError("mutating parser did not persist the force discriminant")

    invalid = [
        (b"", "empty input"), (b"null", "bare null"),
        (b'{"force":0}', "number wrong type"),
        (b'{"force":"true"}', "string wrong type"),
        (b'{"force":fals}', "malformed false"),
        (b'{"force":tru}', "malformed true"),
        (b'{"force":nul}', "malformed null"),
        (b'{"force":true,"force":false}', "duplicate force"),
        (b'{"unknown":true}', "unknown field"),
        (b'{"force":true,"unknown":null}', "unknown extra field"),
        (b'{"f\\u006frce":true}', "escaped key"),
        (b'{"force":true}0', "trailing token"),
        (b'{"force":true,}', "trailing comma"),
        (b" " * 33 + b"{}", "whitespace above 32"),
        (b"x" * 48, "wire above 47"),
    ]
    before = client.view_u64("get")
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    try:
        client.call("commitForce", b'{"force":false,"unknown":null}')
    except NearRpcError:
        pass
    else:
        raise AssertionError("late mutating parse failure unexpectedly succeeded")
    if client.view_u64("get") != before:
        raise AssertionError("late mutating parse failure changed state")
    _expect(client, b"{}", 0)
    _expect(client, b'{"force":true}', 2)
    print("suite NearJsonStorageUnregisterInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-storage-unregister-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
