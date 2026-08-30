#!/usr/bin/env python3
"""Checked little-endian u128 arithmetic scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-token-arithmetic: missing env {name}")
    return value


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    client.deploy(Path(_require("PF_NEAR_WASM")))
    client.call("initialize", b"")

    expected = {
        "addCarryOk": 1,
        "addCarryW0": 0,
        "addCarryW1": 1,
        "addOverflowOk": 0,
        "addOverflowW0": 0,
        "addOverflowW1": 0,
        "addHighOk": 1,
        "addHighW1": 0xFFFFFFFFFFFFFFFE,
        "subBorrowOk": 1,
        "subBorrowW0": 0xFFFFFFFFFFFFFFFF,
        "subBorrowW1": 0,
        "subUnderflowOk": 0,
        "subUnderflowW0": 0xFFFFFFFFFFFFFFFF,
        "subUnderflowW1": 0xFFFFFFFFFFFFFFFF,
        "subHighOk": 1,
        "subHighW1": 1,
    }
    before = client.view_state_values()
    for method, value in expected.items():
        actual = client.view_u64(method)
        if actual != value:
            raise AssertionError(f"{method}: expected {value:#x}, got {actual:#x}")
    if client.view_state_values() != before:
        raise AssertionError("pure arithmetic views changed persistent state")
    print("near-token-arithmetic: carry, borrow, unsigned high limbs, overflow and underflow ok")
    print("suite NearTokenArithmetic: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-token-arithmetic: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
