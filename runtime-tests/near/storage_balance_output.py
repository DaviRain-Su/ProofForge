#!/usr/bin/env python3
"""Exact bounded Option<StorageBalance> JSON output against local nearcore."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-storage-balance-output: missing env {name}")
    return value


def _wire(total: int, available: int) -> bytes:
    return f'{{"total":"{total}","available":"{available}"}}'.encode("ascii")


def _expect(client: NearClient, method: str, expected: bytes) -> None:
    got = client.view(method, b"")
    if got != expected:
        raise AssertionError(f"{method}: expected {expected!r}, got {got!r}")


def _expect_failure(client: NearClient, method: str) -> None:
    try:
        client.view(method, b"")
    except NearRpcError:
        print(f"near-storage-balance-output: {method} trapped ok")
        return
    raise AssertionError(f"{method}: expected view failure")


def main() -> None:
    client = NearClient(
        _require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME"))
    )
    client.deploy(Path(_require("PF_NEAR_WASM")))
    client.call("initialize", NearClient.encode_u64_le(0))

    maximum = (1 << 128) - 1
    cases = {
        "none": b"null",
        "someZero": _wire(0, 0),
        "someTwo64": _wire(1 << 64, 0),
        "someTwo64PlusOne": _wire((1 << 64) + 1, 1 << 64),
        "someAsymmetric": _wire((1 << 64) + 2, (3 << 64) + 7),
        "someMax": _wire(maximum, maximum),
    }
    for method, expected in cases.items():
        _expect(client, method, expected)
    if len(cases["someMax"]) != 105:
        raise AssertionError("maximum StorageBalance wire is not exact 105 bytes")

    # Alternate short and maximum paths to prove the shared arena/scratch has no stale bytes.
    _expect(client, "someMax", cases["someMax"])
    _expect(client, "none", b"null")
    _expect(client, "someZero", cases["someZero"])
    _expect(client, "someAsymmetric", cases["someAsymmetric"])

    for method in (
        "malformedPresence",
        "malformedPresenceMax",
        "malformedNoneTotal",
        "malformedNoneAvailable",
    ):
        _expect_failure(client, method)

    print("near-storage-balance-output: exact null/object/u128 bytes and guards ok")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage-balance-output: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
