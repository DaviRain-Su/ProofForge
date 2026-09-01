#!/usr/bin/env python3
"""Bounded receiver `sender_id`/`amount`/`msg` parser scenes against near-sandbox."""

from __future__ import annotations

import itertools
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-ft-on-transfer-input: missing env {name}")
    return value


def _object(fields: list[tuple[bytes, bytes]], prefix: bytes = b"") -> bytes:
    return prefix + b"{" + b",".join(b'"' + key + b'":' + value for key, value in fields) + b"}"


def _unicode_escape_ascii(value: bytes) -> bytes:
    return b"".join(f"\\u{byte:04x}".encode() for byte in value)


def _expect_u64(client: NearClient, method: str, wire: bytes, expected: int) -> None:
    got = client.view(method, wire)
    encoded = NearClient.encode_u64_le(expected)
    if got != encoded:
        raise AssertionError(f"{method}: expected {encoded.hex()}, got {got.hex()} for {wire!r}")


def _expect_words(client: NearClient, prefix: str, wire: bytes, value: bytes) -> None:
    _expect_u64(client, f"{prefix}Length", wire, len(value))
    frame = value.ljust(64, b"\0")
    for index in range(8):
        _expect_u64(client, f"{prefix}W{index}", wire,
                    int.from_bytes(frame[index * 8:(index + 1) * 8], "little"))


def _expect(client: NearClient, wire: bytes, sender: bytes, amount: int, msg: bytes) -> None:
    _expect_words(client, "sender", wire, sender)
    _expect_u64(client, "amountW0", wire, amount & ((1 << 64) - 1))
    _expect_u64(client, "amountW1", wire, amount >> 64)
    _expect_words(client, "message", wire, msg)


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("senderLength", wire)
    except NearRpcError:
        print(f"near-json-ft-on-transfer-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonFtOnTransferInput (AccountId + u128 + Message64) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    sender = b"sender.test.near"
    amount = (1 << 127) + (1 << 64) + 7
    message = "raw-\u03bb-\U0001f600\0".encode("utf-8")
    fields = [(b"sender_id", b'"sender.test.near"'),
              (b"amount", f'"{amount}"'.encode()),
              (b"msg", b'"raw-\\u03bb-\\ud83d\\ude00\\u0000"')]
    for order in itertools.permutations(fields):
        _expect(client, _object(list(order)), sender, amount, message)
    print("near-json-ft-on-transfer-input: all six field permutations preserved all leaves")

    _expect(client, _object([(b"msg", b'""'), (b"amount", b'"0"'),
                            (b"sender_id", b'"aa"')]), b"aa", 0, b"")
    raw_utf8 = _object([(b"amount", b'"18446744073709551617"'),
                        (b"msg", '"é😀"'.encode()),
                        (b"sender_id", b'"s\\u0065nder.test.near"')])
    _expect(client, raw_utf8, sender, (1 << 64) + 1, "é😀".encode())

    max_account = b"a" * 64
    max_amount = (1 << 128) - 1
    max_message = b"z" * 64
    max_wire = _object([
        (b"sender_id", b'"' + b"\\u0061" * 64 + b'"'),
        (b"amount", b'"' + _unicode_escape_ascii(str(max_amount).encode()) + b'"'),
        (b"msg", b'"' + b"\\u007a" * 64 + b'"'),
    ], b" " * 32)
    if len(max_wire) != 1071:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 1071")
    _expect(client, max_wire, max_account, max_amount, max_message)

    invalid = [
        (b"{}", "missing all fields"),
        (_object(fields[1:]), "missing sender"),
        (_object([fields[0], fields[2]]), "missing amount"),
        (_object(fields[:2]), "missing message"),
        (_object(fields + [fields[0]]), "duplicate sender"),
        (_object(fields + [fields[1]]), "duplicate amount"),
        (_object(fields + [fields[2]]), "duplicate message"),
        (_object(fields + [(b"memo", b"null")]), "unknown field"),
        (_object([(b"s\\u0065nder_id", fields[0][1]), fields[1], fields[2]]), "escaped key"),
        (_object([(b"sender_id", b"null"), fields[1], fields[2]]), "sender null"),
        (_object([fields[0], (b"amount", b"1"), fields[2]]), "amount wrong type"),
        (_object([fields[0], fields[1], (b"msg", b"null")]), "message null"),
        (_object([(b"sender_id", b'"a"'), fields[1], fields[2]]), "short sender"),
        (_object([(b"sender_id", b'"' + b"a" * 65 + b'"'), fields[1], fields[2]]), "long sender"),
        (_object([(b"sender_id", b'"Alice.near"'), fields[1], fields[2]]), "invalid account syntax"),
        (_object([fields[0], (b"amount", b'"01"'), fields[2]]), "leading-zero amount"),
        (_object([fields[0], (b"amount", b'"340282366920938463463374607431768211456"'), fields[2]]), "amount overflow"),
        (_object([fields[0], fields[1], (b"msg", b'"' + b"x" * 65 + b'"')]), "65-byte raw message"),
        (_object([fields[0], fields[1], (b"msg", b'"' + b"\\u0078" * 65 + b'"')]), "65-byte escaped message"),
        (_object([fields[0], fields[1], (b"msg", b'"\\ud83d"')]), "lone high surrogate"),
        (_object([fields[0], fields[1], (b"msg", b'"\\ude00\\ud83d"')]), "reversed surrogate pair"),
        (_object([fields[0], fields[1], (b"msg", b'"\\u00xz"')]), "invalid hex escape"),
        (_object([fields[0], fields[1], (b"msg", b'"\x01"')]), "raw control byte"),
        (_object([fields[0], fields[1], (b"msg", b'"\xf0\x28\x8c\x28"')]), "malformed UTF-8"),
        (_object(fields) + b"0", "trailing token"),
        (b" " * 33 + _object(fields), "whitespace above 32"),
        (max_wire + b"0", "wire above exact 1071 bound"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)

    # A late parse failure and prior max frame cannot leak active bytes into a following short call.
    _expect(client, _object([(b"msg", b'"q"'), (b"amount", b'"9"'),
                            (b"sender_id", b'"aa"')]), b"aa", 9, b"q")

    committed = client.call("commitAmountHigh", _object(fields))
    if NearClient.success_value_bytes(committed) != NearClient.encode_u64_le(amount >> 64):
        raise AssertionError("mutating receiver parser returned the wrong amount high limb")
    if client.view_u64("get") != amount >> 64:
        raise AssertionError("mutating receiver parser did not persist the amount high limb")
    client.call("commitAmountHigh", _object(fields) + b"0", expect_success=False)
    if client.view_u64("get") != amount >> 64:
        raise AssertionError("failed receiver argument parse changed state")

    print("near-json-ft-on-transfer-input: bounds, Unicode, inactive zeros, stale isolation, and rollback ok")
    print("suite NearJsonFtOnTransferInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-ft-on-transfer-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
