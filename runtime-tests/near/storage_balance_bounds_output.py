#!/usr/bin/env python3
"""Exact bounded StorageBalanceBounds JSON output against local nearcore."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-storage-balance-bounds-output: missing env {name}")
    return value


def _wire(minimum: int, maximum: int | None) -> bytes:
    max_wire = "null" if maximum is None else f'"{maximum}"'
    return f'{{"min":"{minimum}","max":{max_wire}}}'.encode("ascii")


def _expect(client: NearClient, method: str, expected: bytes) -> None:
    before = client.view_state_values("test.near")
    got = client.view(method, b"")
    if got != expected:
        raise AssertionError(f"{method}: expected {expected!r}, got {got!r}")
    if client.view_state_values("test.near") != before:
        raise AssertionError(f"{method}: view changed state")


def _expect_failure(client: NearClient, method: str) -> None:
    before = client.view_state_values("test.near")
    try:
        client.view(method, b"")
    except NearRpcError:
        if client.view_state_values("test.near") != before:
            raise AssertionError(f"{method}: failed view changed state")
        print(f"near-storage-balance-bounds-output: {method} trapped ok")
        return
    raise AssertionError(f"{method}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    client.deploy(Path(_require("PF_NEAR_WASM")))
    client.call("initialize", NearClient.encode_u64_le(0))

    maximum = (1 << 128) - 1
    cases = {
        "noMaxZero": _wire(0, None),
        "noMaxTwo64": _wire(1 << 64, None),
        "someZero": _wire(0, 0),
        "someTwo64PlusOne": _wire((1 << 64) + 1, 1 << 64),
        "someAsymmetric": _wire((1 << 64) + 2, (3 << 64) + 7),
        "someMax": _wire(maximum, maximum),
    }
    for method, expected in cases.items():
        _expect(client, method, expected)
    if len(cases["someMax"]) != 97:
        raise AssertionError("maximum StorageBalanceBounds wire is not exact 97 bytes")
    if len(_wire(maximum, None)) != 60:
        raise AssertionError("maximum unbounded StorageBalanceBounds wire is not exact 60 bytes")

    # Alternate maximum/short and Some/None paths to prove arena/scratch stale isolation.
    _expect(client, "someMax", cases["someMax"])
    _expect(client, "noMaxZero", cases["noMaxZero"])
    _expect(client, "someZero", cases["someZero"])
    _expect(client, "noMaxTwo64", cases["noMaxTwo64"])
    _expect(client, "someAsymmetric", cases["someAsymmetric"])

    for method in (
        "malformedPresence",
        "malformedPresenceMax",
        "malformedNoneMaxLow",
        "malformedNoneMaxHigh",
    ):
        _expect_failure(client, method)

    print("near-storage-balance-bounds-output: exact object/u128/null bytes and guards ok")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage-balance-bounds-output: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
