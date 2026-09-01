#!/usr/bin/env python3
"""ProofForge bounded persistent Queue scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


PREFIX = b"QUE1"
CAPACITY = 3


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-queue: missing env {name}")
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


def _expect_slot(state: dict[bytes, bytes], index: int, value: int) -> None:
    expected = NearClient.encode_u64_le(value)
    actual = state.get(_key(index))
    if actual != expected:
        raise AssertionError(
            f"slot {index}: expected key={_key(index)!r} value={expected.hex()}, got {actual!r}"
        )


def _queue_keys(state: dict[bytes, bytes]) -> set[bytes]:
    return {key for key in state if len(key) == 8 and key.startswith(PREFIX)}


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearQueue (ProofForge bounded persistent FIFO) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    initial = client.view_state_values()
    if client.view_u64("get") != 0 or client.view_u64("getHead") != 0:
        raise AssertionError("new queue must have canonical head=length=0")
    if client.view_u64("peek") != 0:
        raise AssertionError("empty peek must return its explicit zero fallback")
    if client.view_u64("hasAt", NearClient.encode_u64_le(0)) != 0:
        raise AssertionError("empty queue must not expose an active offset")
    client.call("pop", b"", expect_success=False)
    if client.view_state_values() != initial:
        raise AssertionError("empty pop failure must roll back byte-exact state")
    print("near-queue: canonical empty state, bounds, and rollback ok")

    values = (0, 11, 22)
    for expected_length, value in enumerate(values, start=1):
        if _call_u64(client, "push", value) != expected_length:
            raise AssertionError(f"push({value}) did not return length {expected_length}")
    if client.view_u64("get") != CAPACITY or client.view_u64("getHead") != 0:
        raise AssertionError("three pushes must fill the ring at head zero")
    for offset, value in enumerate(values):
        encoded_offset = NearClient.encode_u64_le(offset)
        if client.view_u64("hasAt", encoded_offset) != 1:
            raise AssertionError(f"active offset {offset} must have a durable key")
        if client.view_u64("getAt", encoded_offset) != value:
            raise AssertionError(f"logical offset {offset} did not preserve FIFO value {value}")
    state = client.view_state_values()
    for index, value in enumerate(values):
        _expect_slot(state, index, value)
    if client.view_u64("peek") != 0 or client.view_u64(
        "hasAt", NearClient.encode_u64_le(0)
    ) != 1:
        raise AssertionError("stored zero must remain distinguishable from absence through hasAt")
    print("near-queue: exact QUE1||u32_le slots, Borsh values, FIFO, and zero presence ok")

    full = client.view_state_values()
    client.call("push", NearClient.encode_u64_le(33), expect_success=False)
    if client.view_state_values() != full:
        raise AssertionError("push at capacity must roll back byte-exact state")
    large = (1 << 32) + 1
    if client.view_u64("getAt", NearClient.encode_u64_le(large)) != 0:
        raise AssertionError("large logical offset aliased a narrowed u32 physical suffix")
    if client.view_u64("hasAt", NearClient.encode_u64_le(large)) != 0:
        raise AssertionError("large logical offset unexpectedly reached durable storage")
    print("near-queue: capacity and pre-key-construction offset guards ok")

    if _call_u64(client, "pop") != 2:
        raise AssertionError("first pop must return remaining length 2")
    state = client.view_state_values()
    if _key(0) in state or client.view_u64("getHead") != 1:
        raise AssertionError("first pop must reclaim slot 0 and advance head to 1")
    if client.view_u64("peek") != 11:
        raise AssertionError("FIFO front after removing zero must be 11")

    if _call_u64(client, "push", 33) != 3:
        raise AssertionError("push after pop must refill the queue")
    state = client.view_state_values()
    _expect_slot(state, 0, 33)
    _expect_slot(state, 1, 11)
    _expect_slot(state, 2, 22)
    if [client.view_u64("getAt", NearClient.encode_u64_le(i)) for i in range(3)] != [
        11,
        22,
        33,
    ]:
        raise AssertionError("wrapped ring did not preserve logical FIFO order")
    print("near-queue: tail wraparound reuses reclaimed slot without changing FIFO order")

    for expected_front, expected_length, expected_head, removed_slot in (
        (11, 2, 2, 1),
        (22, 1, 0, 2),
        (33, 0, 0, 0),
    ):
        if client.view_u64("peek") != expected_front:
            raise AssertionError(f"expected FIFO front {expected_front} before pop")
        if _call_u64(client, "pop") != expected_length:
            raise AssertionError(f"pop must return remaining length {expected_length}")
        state = client.view_state_values()
        if _key(removed_slot) in state:
            raise AssertionError(f"pop did not physically reclaim slot {removed_slot}")
        if client.view_u64("getHead") != expected_head:
            raise AssertionError(f"expected head {expected_head} after pop")
    state = client.view_state_values()
    if client.view_u64("get") != 0 or _queue_keys(state):
        raise AssertionError("drained queue must reset metadata and reclaim every element key")
    print("near-queue: FIFO pops, head wrap, drained reset, and complete reclamation ok")

    if _call_u64(client, "malform") != 99:
        raise AssertionError("malform fixture did not install its sentinel metadata")
    malformed = client.view_state_values()
    if client.view_u64("get") != 1 or client.view_u64("getHead") != CAPACITY:
        raise AssertionError("malform fixture did not create head==capacity,length==1")
    if client.view_u64("peek") != 0 or client.view_u64(
        "hasAt", NearClient.encode_u64_le(0)
    ) != 0:
        raise AssertionError("malformed metadata must fail closed before raw storage access")
    client.call("push", NearClient.encode_u64_le(44), expect_success=False)
    client.call("pop", b"", expect_success=False)
    if client.view_state_values() != malformed or _queue_keys(malformed):
        raise AssertionError("malformed push/pop must preserve state and create no queue key")
    print("near-queue: malformed metadata fails closed for views and mutations")
    print("suite NearQueue: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-queue: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
