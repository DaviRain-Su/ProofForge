#!/usr/bin/env python3
"""Bounded direct-write Vector scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


PREFIX = b"VEC1"


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-vector: missing env {name}")
    return value


def _key(index: int) -> bytes:
    return PREFIX + index.to_bytes(4, "little")


def _call_u64(client: NearClient, method: str, value: int | None = None) -> int:
    args = b"" if value is None else NearClient.encode_u64_le(value)
    result = client.call(method, args)
    raw = NearClient.success_value_bytes(result)
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected 8-byte SuccessValue, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def _expect_element(state: dict[bytes, bytes], index: int, value: int) -> None:
    expected = NearClient.encode_u64_le(value)
    actual = state.get(_key(index))
    if actual != expected:
        raise AssertionError(
            f"element {index}: expected key={_key(index)!r} value={expected.hex()}, "
            f"got {actual!r}"
        )


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearVector (bounded direct-write / current element layout) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    initial = client.view_state_values()
    if client.view_u64("get") != 0 or client.view_u64(
        "getAt", NearClient.encode_u64_le(0)
    ) != 0:
        raise AssertionError("new vector must be empty and out-of-range getAt must default to zero")
    client.call("setFirst", NearClient.encode_u64_le(9), expect_success=False)
    client.call("pop", b"", expect_success=False)
    if client.view_state_values() != initial:
        raise AssertionError("empty set/pop failures must roll back byte-exact state")
    print("near-vector: empty bounds and rollback ok")

    first = 0x0102030405060708
    second = 0xFFEEDDCCBBAA0099
    if _call_u64(client, "push", first) != 1:
        raise AssertionError("first push must return length 1")
    if _call_u64(client, "push", second) != 2:
        raise AssertionError("second push must return length 2")
    if client.view_u64("get") != 2:
        raise AssertionError("two pushes must persist logical length 2")
    if client.view_u64("getAt", NearClient.encode_u64_le(0)) != first:
        raise AssertionError("getAt(0) did not decode the first Borsh UInt64")
    if client.view_u64("getAt", NearClient.encode_u64_le(1)) != second:
        raise AssertionError("getAt(1) did not decode the second Borsh UInt64")
    state = client.view_state_values()
    _expect_element(state, 0, first)
    _expect_element(state, 1, second)
    print("near-vector: exact prefix||u32_le keys and Borsh-u64 values ok")

    replacement = 0x8877665544332211
    if _call_u64(client, "setFirst", replacement) != replacement:
        raise AssertionError("setFirst must return the replacement value")
    if client.view_u64("getAt", NearClient.encode_u64_le(0)) != replacement:
        raise AssertionError("setFirst replacement was not immediately visible")
    state = client.view_state_values()
    _expect_element(state, 0, replacement)
    _expect_element(state, 1, second)
    print("near-vector: bounded set and immediate same-transaction layout ok")

    if _call_u64(client, "pop") != 1:
        raise AssertionError("pop from length 2 must return length 1")
    state = client.view_state_values()
    if _key(1) in state:
        raise AssertionError("pop did not reclaim the last durable element key")
    _expect_element(state, 0, replacement)
    if client.view_u64("getAt", NearClient.encode_u64_le(1)) != 0:
        raise AssertionError("popped index must be out of range and default to zero")
    print("near-vector: pop removes the last element and updates logical length ok")

    for value in (30, 40, 50):
        _call_u64(client, "push", value)
    if client.view_u64("get") != 4:
        raise AssertionError("vector did not reach its compile-time capacity")
    full = client.view_state_values()
    client.call("push", NearClient.encode_u64_le(60), expect_success=False)
    if client.view_state_values() != full:
        raise AssertionError("push at capacity must roll back byte-exact state")
    if client.view_u64("getAt", NearClient.encode_u64_le(1 << 32 | 1)) != 0:
        raise AssertionError("large out-of-range index aliased a narrowed u32 suffix")
    print("near-vector: capacity failure and pre-narrowing index guard ok")
    print("suite NearVector: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-vector: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
