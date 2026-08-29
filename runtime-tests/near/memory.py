#!/usr/bin/env python3
"""Invocation-local Wasm arena scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-memory: missing env {name}")
    return value


def _expect_failure(client: NearClient, method: str) -> None:
    try:
        client.view(method, b"")
    except NearRpcError:
        print(f"near-memory: {method} trapped ok")
        return
    raise AssertionError(f"{method}: expected view failure")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearMemory (guest Wasm arena) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    for value in (1, 0x123456789ABCDEF0):
        got = client.view_u64("roundTrip", NearClient.encode_u64_le(value))
        if got != value:
            raise AssertionError(f"roundTrip({value:#x}) expected same value, got {got:#x}")
    print("near-memory: bounded allocation/set/get and invocation reset ok")

    for _ in range(2):
        if client.view_u64("startsZero") != 0:
            raise AssertionError("new Buffer64 must be zero initialized")
    print("near-memory: reused invocation memory is zero initialized ok")

    for value in (7, 99):
        got = client.view_u64("growAndReuse", NearClient.encode_u64_le(value))
        if got != value:
            raise AssertionError(f"growAndReuse({value}) expected same value, got {got}")
    print("near-memory: two 32-KiB non-reclaiming allocations and reuse ok")

    for method in ("outOfBounds", "staleHandle", "wrongCapacity", "doubleBegin"):
        _expect_failure(client, method)

    print("suite NearMemory: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-memory: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
