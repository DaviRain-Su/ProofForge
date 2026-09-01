#!/usr/bin/env python3
"""Bounded optional-u128 storage-withdraw JSON argument scenes against local nearcore."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-storage-withdraw-input: missing env {name}")
    return value


def _view_u64(client: NearClient, method: str, wire: bytes) -> int:
    raw = client.view(method, wire)
    if len(raw) != 8:
        raise AssertionError(f"{method}: expected 8 bytes, got {raw!r}")
    return int.from_bytes(raw, "little")


def _expect(client: NearClient, wire: bytes, present: int, value: int) -> None:
    mask = (1 << 64) - 1
    got = (
        _view_u64(client, "amountPresent", wire),
        _view_u64(client, "amountW0", wire),
        _view_u64(client, "amountW1", wire),
    )
    expected = (present, value & mask, value >> 64)
    if got != expected:
        raise AssertionError(f"{wire!r}: expected frame {expected}, got {got}")


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("amountPresent", wire)
    except NearRpcError:
        print(f"near-json-storage-withdraw-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def _wire(digits: bytes) -> bytes:
    return b'{"amount":"' + digits + b'"}'


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonStorageWithdrawInput (optional amount) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(9))

    for wire in (b"{}", b'{"amount":null}', b' { "amount" : null } '):
        _expect(client, wire, 0, 0)
    values = (0, 1 << 64, (1 << 64) + 1, (7 << 64) + 11, (1 << 128) - 1)
    for value in values:
        _expect(client, _wire(str(value).encode()), 1, value)
    _expect(client, _wire(b"\\u0031\\u0032\\u0033"), 1, 123)

    max_digits = str((1 << 128) - 1).encode()
    max_escaped = b"".join(b"\\u00" + bytes(f"{digit:02x}", "ascii") for digit in max_digits)
    max_wire = b" " * 32 + _wire(max_escaped)
    if len(max_wire) != 279:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 279")
    _expect(client, max_wire, 1, (1 << 128) - 1)

    result = client.call("commitW1", _wire(str((7 << 64) + 9).encode()))
    if NearClient.success_value_bytes(result) != NearClient.encode_u64_le(7):
        raise AssertionError("mutating parser returned the wrong high limb")
    if client.view_u64("get") != 7:
        raise AssertionError("mutating parser did not persist the high limb")

    invalid = [
        (b"", "empty input"), (b"null", "bare null"),
        (_wire(b""), "empty decimal"), (_wire(b"+1"), "plus sign"),
        (_wire(b"-1"), "minus sign"), (_wire(b"00"), "leading zero"),
        (_wire(str(1 << 128).encode()), "max plus one"),
        (_wire(b"9" * 39), "39-digit overflow"), (_wire(b"1" * 40), "40 digits"),
        (b'{"amount":0}', "wrong number type"), (b'{"amount":false}', "wrong boolean type"),
        (b'{"amount":"1","amount":"2"}', "duplicate field"),
        (b'{"unknown":"1"}', "unknown field"),
        (b'{"amount":"1","unknown":null}', "unknown extra field"),
        (b'{"am\\u006funt":"1"}', "escaped key"),
        (b'{"amount":"1"', "truncated object"),
        (b'{"amount":nul}', "truncated null"),
        (b'{"amount":"1"}0', "trailing token"),
        (b'{"amount":"1",}', "trailing comma"),
        (b" " * 33 + b"{}", "whitespace above 32"),
        (max_wire + b" ", "wire above 279"),
        (b'{"amount":"\\u00xz"}', "bad hex"),
        (b'{"amount":"\\ud800"}', "surrogate"),
        (b'{"amount":"\xff"}', "invalid UTF-8"),
    ]
    before = client.view_u64("get")
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    try:
        client.call("commitW1", b'{"amount":"2","unknown":null}')
    except NearRpcError:
        pass
    else:
        raise AssertionError("late mutating parse failure unexpectedly succeeded")
    if client.view_u64("get") != before:
        raise AssertionError("late mutating parse failure changed state")

    # Alternate maximum and inactive frames to prove invocation-local clearing and no stale limbs.
    _expect(client, max_wire, 1, (1 << 128) - 1)
    _expect(client, b"{}", 0, 0)
    _expect(client, _wire(b"0"), 1, 0)
    _expect(client, b'{"amount":null}', 0, 0)
    print("suite NearJsonStorageWithdrawInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-storage-withdraw-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
