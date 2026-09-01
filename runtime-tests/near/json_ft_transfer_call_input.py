#!/usr/bin/env python3
"""Bounded four-field transfer-call JSON parser scenes against near-sandbox."""

from __future__ import annotations

import itertools
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-ft-transfer-call-input: missing env {name}")
    return value


def _object(fields: list[tuple[bytes, bytes]], prefix: bytes = b"") -> bytes:
    return prefix + b"{" + b",".join(b'"' + k + b'":' + v for k, v in fields) + b"}"


def _esc(value: bytes) -> bytes:
    return b"".join(f"\\u{byte:04x}".encode() for byte in value)


def _u64(client: NearClient, method: str, wire: bytes, expected: int) -> None:
    got = client.view(method, wire)
    want = NearClient.encode_u64_le(expected)
    if got != want:
        raise AssertionError(f"{method}: expected {want.hex()}, got {got.hex()}")


def _expect(client: NearClient, wire: bytes, receiver: bytes, amount: int,
            memo_present: int, memo: bytes, msg: bytes) -> None:
    receiver_frame = receiver.ljust(64, b"\0")
    msg_frame = msg.ljust(64, b"\0")
    memo_frame = memo.ljust(16, b"\0")
    _u64(client, "receiverLength", wire, len(receiver))
    _u64(client, "receiverW0", wire, int.from_bytes(receiver_frame[:8], "little"))
    _u64(client, "receiverW7", wire, int.from_bytes(receiver_frame[56:], "little"))
    _u64(client, "amountW0", wire, amount & ((1 << 64) - 1))
    _u64(client, "amountW1", wire, amount >> 64)
    _u64(client, "memoPresent", wire, memo_present)
    _u64(client, "memoLength", wire, len(memo))
    _u64(client, "memoW1", wire, int.from_bytes(memo_frame[8:], "little"))
    _u64(client, "messageLength", wire, len(msg))
    _u64(client, "messageW0", wire, int.from_bytes(msg_frame[:8], "little"))
    _u64(client, "messageW7", wire, int.from_bytes(msg_frame[56:], "little"))


def _reject(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("messageLength", wire)
    except NearRpcError:
        print(f"near-json-ft-transfer-call-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonFtTransferCallInput (four-field bounded loop) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    receiver = b"receiver.test.near"
    amount = (1 << 127) + (1 << 64) + 7
    memo = "é雪".encode()
    msg = b"child\0" + "😀".encode()
    fields = [
        (b"receiver_id", b'"receiver.test.near"'),
        (b"amount", f'"{amount}"'.encode()),
        (b"memo", b'"\\u00e9\\u96ea"'),
        (b"msg", b'"child\\u0000\\ud83d\\ude00"'),
    ]
    for order in itertools.permutations(fields):
        _expect(client, _object(list(order)), receiver, amount, 1, memo, msg)
    for order in itertools.permutations([fields[0], fields[1], fields[3]]):
        _expect(client, _object(list(order)), receiver, amount, 0, b"", msg)
    _expect(client, _object([fields[3], fields[0], (b"memo", b"null"), fields[1]]),
            receiver, amount, 0, b"", msg)
    _expect(client, _object([fields[1], (b"msg", b'""'), (b"memo", b'""'), fields[0]]),
            receiver, amount, 1, b"", b"")

    maximum = (1 << 128) - 1
    max_wire = _object([
        (b"receiver_id", b'"' + b"\\u0061" * 64 + b'"'),
        (b"amount", b'"' + _esc(str(maximum).encode()) + b'"'),
        (b"memo", b'"' + b"\\u0061" * 16 + b'"'),
        (b"msg", b'"' + b"\\u0062" * 64 + b'"'),
    ], b" " * 32)
    if len(max_wire) != 1179:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 1179")
    _expect(client, max_wire, b"a" * 64, maximum, 1, b"a" * 16, b"b" * 64)

    required = [fields[0], fields[1], fields[3]]
    invalid = [
        (b"{}", "missing required fields"),
        (_object(required[:2]), "missing msg"),
        (_object(required[1:]), "missing receiver"),
        (_object([required[0], required[2]]), "missing amount"),
        (_object(required + [required[2]]), "duplicate msg"),
        (_object(required + [fields[0]]), "duplicate receiver"),
        (_object(required + [fields[1]]), "duplicate amount"),
        (_object(required + [fields[2], fields[2]]), "duplicate memo"),
        (_object(required + [(b"other", b"0")]), "unknown field"),
        (_object([(b"m\\u0073g", b'"x"'), fields[0], fields[1]]), "escaped key"),
        (_object([fields[0], fields[1], (b"msg", b"null")]), "null msg"),
        (_object([fields[0], fields[1], (b"msg", b"1")]), "wrong msg type"),
        (_object([fields[0], fields[1], (b"msg", b'"' + b"a" * 65 + b'"')]), "msg above 64"),
        (_object([fields[0], fields[1], (b"msg", b'"\\ud83d"')]), "isolated surrogate"),
        (_object([fields[0], fields[1], (b"msg", b'"\xff"')]), "malformed UTF-8"),
        (_object([(b"receiver_id", b'"a"'), fields[1], fields[3]]), "short account"),
        (_object([fields[0], (b"amount", b'"01"'), fields[3]]), "noncanonical amount"),
        (_object(required) + b"0", "trailing token"),
        (b" " * 33 + _object(required), "whitespace above 32"),
        (max_wire + b"0", "wire above 1179"),
    ]
    for wire, scene in invalid:
        _reject(client, wire, scene)

    # A late failed parse cannot leak maximum-frame bytes into the next short invocation.
    short = _object([(b"msg", b'"z"'), (b"amount", b'"9"'),
                     (b"receiver_id", b'"aa"')])
    _expect(client, short, b"aa", 9, 0, b"", b"z")
    response = client.call("commitMessageLength", _object(fields))
    if NearClient.success_value_bytes(response) != NearClient.encode_u64_le(len(msg)):
        raise AssertionError("mutating parser returned wrong committed message length")
    if client.view_u64("get") != len(msg):
        raise AssertionError("mutating parser did not persist message length")
    client.call("commitMessageLength", _object(fields) + b"0", expect_success=False)
    if client.view_u64("get") != len(msg):
        raise AssertionError("failed late parse changed state")
    print("near-json-ft-transfer-call-input: permutations, bounds, Unicode, stale isolation, rollback ok")
    print("suite NearJsonFtTransferCallInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-ft-transfer-call-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
