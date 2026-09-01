#!/usr/bin/env python3
"""Mutating exact JSON Boolean output scenes against near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-boolean-mutation: missing env {name}")
    return value


def _call(client: NearClient, value: int, expected: bytes) -> None:
    result = client.call("setChecked", NearClient.encode_u64_le(value))
    got = NearClient.success_value_bytes(result)
    if got != expected:
        raise AssertionError(f"value {value}: expected {expected!r}, got {got!r}")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonBooleanMutation (exact true/false) ===")
    client.deploy(wasm)
    client.call("initialize", b"")

    _call(client, 0, b"false")
    if client.view_u64("left") != 11 or client.view_u64("right") != 22:
        raise AssertionError("false result did not persist both independent state fields")
    _call(client, 1, b"true")
    if client.view_u64("left") != 11 or client.view_u64("right") != 22:
        raise AssertionError("true result corrupted independent state fields")

    before = (client.view_u64("left"), client.view_u64("right"))
    try:
        client.call("setChecked", NearClient.encode_u64_le(2))
    except NearRpcError:
        pass
    else:
        raise AssertionError("out-of-range Boolean discriminant unexpectedly succeeded")
    after = (client.view_u64("left"), client.view_u64("right"))
    if after != before:
        raise AssertionError(f"post-write output failure did not roll back state: {before} -> {after}")
    _call(client, 0, b"false")
    _call(client, 1, b"true")
    print("suite NearJsonBooleanMutation: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-boolean-mutation: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
