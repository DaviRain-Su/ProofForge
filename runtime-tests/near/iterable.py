#!/usr/bin/env python3
"""Identity IterableMap/IterableSet scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


MAP_VECTOR = b"IMPv"
MAP_LOOKUP = b"IMPm"
SET_VECTOR = b"ITSv"
SET_LOOKUP = b"ITSm"
CAPACITY = 3


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-iterable: missing env {name}")
    return value


def _u32(value: int) -> bytes:
    return value.to_bytes(4, "little")


def _u64(value: int) -> bytes:
    return value.to_bytes(8, "little")


def _vector_key(prefix: bytes, index: int) -> bytes:
    return prefix + _u32(index)


def _lookup_key(prefix: bytes, key: int) -> bytes:
    return prefix + _u64(key)


def _map_record(value: int, index: int) -> bytes:
    return _u64(value) + _u32(index)


def _packed(key: int, value: int) -> int:
    if not 0 <= key <= 0xFFFFFFFF or not 0 <= value <= 0xFFFFFFFF:
        raise ValueError("fixture mapPut packs two UInt32 test words")
    return key | (value << 32)


def _call_u64(client: NearClient, method: str, value: int | None = None) -> int:
    args = b"" if value is None else NearClient.encode_u64_le(value)
    result = client.call(method, args)
    raw = NearClient.success_value_bytes(result)
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected 8-byte SuccessValue, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def _view(client: NearClient, method: str, value: int) -> int:
    return client.view_u64(method, NearClient.encode_u64_le(value))


def _expect(state: dict[bytes, bytes], key: bytes, value: bytes) -> None:
    actual = state.get(key)
    if actual != value:
        raise AssertionError(f"key {key!r}: expected {value.hex()}, got {actual!r}")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearIterable (Identity IterableMap/IterableSet) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    initial = client.view_state_values()
    if client.view_u64("mapLen") != 0 or client.view_u64("setLen") != 0:
        raise AssertionError("new iterable collections must be empty")
    if _view(client, "mapIndex", 7) != CAPACITY or _view(client, "setIndex", 5) != CAPACITY:
        raise AssertionError("absent lookup must return the capacity sentinel")
    client.call("mapRemove", NearClient.encode_u64_le(7), expect_success=False)
    client.call("setRemove", NearClient.encode_u64_le(5), expect_success=False)
    if client.view_state_values() != initial:
        raise AssertionError("absent removals must roll back byte-exact state")
    print("near-iterable: canonical empty state, absence sentinel, and rollback ok")

    for length, (key, value) in enumerate(((7, 70), (9, 90), (11, 110)), start=1):
        if _call_u64(client, "mapPut", _packed(key, value)) != length:
            raise AssertionError(f"map insert {key} did not return length {length}")
    if client.view_u64("mapLen") != CAPACITY:
        raise AssertionError("three fresh map inserts must fill capacity")
    state = client.view_state_values()
    for index, (key, value) in enumerate(((7, 70), (9, 90), (11, 110))):
        _expect(state, _vector_key(MAP_VECTOR, index), _u64(key))
        _expect(state, _lookup_key(MAP_LOOKUP, key), _map_record(value, index))
        if _view(client, "mapKeyAt", index) != key or _view(client, "mapIndex", key) != index:
            raise AssertionError("map vector order and lookup index disagree")
        if _view(client, "mapGet", key) != value or _view(client, "mapHasKeyAt", index) != 1:
            raise AssertionError("map view did not preserve value or vector presence")
    print("near-iterable: exact Identity map vector/lookup bytes and index records ok")

    before_replace = client.view_state_values()
    if _call_u64(client, "mapPut", _packed(9, 99)) != CAPACITY:
        raise AssertionError("map replacement must preserve length")
    state = client.view_state_values()
    _expect(state, _lookup_key(MAP_LOOKUP, 9), _map_record(99, 1))
    for index, key in enumerate((7, 9, 11)):
        _expect(state, _vector_key(MAP_VECTOR, index), _u64(key))
    if set(before_replace) != set(state):
        raise AssertionError("map replacement changed durable key membership")
    full = state
    client.call("mapPut", NearClient.encode_u64_le(_packed(13, 130)), expect_success=False)
    if client.view_state_values() != full:
        raise AssertionError("map insert at capacity must roll back byte-exact state")
    print("near-iterable: replacement preserves order/index and full insert rolls back")

    if _call_u64(client, "mapRemove", 9) != 2:
        raise AssertionError("map swap-remove must return length 2")
    state = client.view_state_values()
    _expect(state, _vector_key(MAP_VECTOR, 0), _u64(7))
    _expect(state, _vector_key(MAP_VECTOR, 1), _u64(11))
    _expect(state, _lookup_key(MAP_LOOKUP, 11), _map_record(110, 1))
    if _lookup_key(MAP_LOOKUP, 9) in state or _vector_key(MAP_VECTOR, 2) in state:
        raise AssertionError("map swap-remove did not reclaim target lookup and old last slot")
    if _view(client, "mapIndex", 11) != 1 or _view(client, "mapGet", 11) != 110:
        raise AssertionError("map moved record was not repaired")
    if _call_u64(client, "mapRemove", 11) != 1:
        raise AssertionError("map tail remove must return length 1")
    state = client.view_state_values()
    if _lookup_key(MAP_LOOKUP, 11) in state or _vector_key(MAP_VECTOR, 1) in state:
        raise AssertionError("map tail remove did not reclaim both keys")
    print("near-iterable: map swap-remove, moved-index repair, tail remove, and reclamation ok")

    for length, value in enumerate((5, 6, 7), start=1):
        if _call_u64(client, "setInsert", value) != length:
            raise AssertionError(f"set insert {value} did not return length {length}")
    before_duplicate = client.view_state_values()
    if _call_u64(client, "setInsert", 6) != CAPACITY:
        raise AssertionError("duplicate set insert must preserve length")
    if client.view_state_values() != before_duplicate:
        raise AssertionError("duplicate set insert must not change durable state")
    state = client.view_state_values()
    for index, value in enumerate((5, 6, 7)):
        _expect(state, _vector_key(SET_VECTOR, index), _u64(value))
        _expect(state, _lookup_key(SET_LOOKUP, value), _u32(index))
        if _view(client, "setKeyAt", index) != value or _view(client, "setIndex", value) != index:
            raise AssertionError("set vector order and lookup index disagree")
    full = state
    client.call("setInsert", NearClient.encode_u64_le(8), expect_success=False)
    if client.view_state_values() != full:
        raise AssertionError("set insert at capacity must roll back byte-exact state")
    print("near-iterable: exact Identity set bytes, duplicate no-op, and capacity rollback ok")

    if _call_u64(client, "setRemove", 6) != 2:
        raise AssertionError("set swap-remove must return length 2")
    state = client.view_state_values()
    _expect(state, _vector_key(SET_VECTOR, 1), _u64(7))
    _expect(state, _lookup_key(SET_LOOKUP, 7), _u32(1))
    if _lookup_key(SET_LOOKUP, 6) in state or _vector_key(SET_VECTOR, 2) in state:
        raise AssertionError("set swap-remove did not reclaim target lookup and old last slot")
    if _call_u64(client, "setRemove", 7) != 1:
        raise AssertionError("set tail remove must return length 1")
    print("near-iterable: set swap-remove, moved-index repair, tail remove, and reclamation ok")

    if _call_u64(client, "corruptMap7") != 77:
        raise AssertionError("map corruption fixture did not run")
    malformed_map = client.view_state_values()
    if _view(client, "mapIndex", 7) != CAPACITY + 1:
        raise AssertionError("out-of-capacity map index must decode as malformed sentinel")
    client.call("mapPut", NearClient.encode_u64_le(_packed(7, 700)), expect_success=False)
    client.call("mapRemove", NearClient.encode_u64_le(7), expect_success=False)
    if client.view_state_values() != malformed_map:
        raise AssertionError("malformed map mutations must roll back byte-exact state")

    if _call_u64(client, "corruptSet5") != 55:
        raise AssertionError("set corruption fixture did not run")
    malformed_set = client.view_state_values()
    if _view(client, "setIndex", 5) != CAPACITY + 1:
        raise AssertionError("out-of-capacity set index must decode as malformed sentinel")
    client.call("setInsert", NearClient.encode_u64_le(5), expect_success=False)
    client.call("setRemove", NearClient.encode_u64_le(5), expect_success=False)
    if client.view_state_values() != malformed_set:
        raise AssertionError("malformed set mutations must roll back byte-exact state")
    print("near-iterable: malformed index records fail closed before mutation")
    print("suite NearIterable: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-iterable: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
