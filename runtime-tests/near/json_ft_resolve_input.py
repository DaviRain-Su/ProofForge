#!/usr/bin/env python3
"""Bounded private-resolver JSON argument parser scenes against near-sandbox."""

from __future__ import annotations

import itertools
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-ft-resolve-input: missing env {name}")
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


def _expect_account(client: NearClient, prefix: str, wire: bytes, account: bytes) -> None:
    _expect_u64(client, f"{prefix}Length", wire, len(account))
    frame = account.ljust(64, b"\0")
    for index in range(8):
        _expect_u64(
            client,
            f"{prefix}W{index}",
            wire,
            int.from_bytes(frame[index * 8:(index + 1) * 8], "little"),
        )


def _expect(client: NearClient, wire: bytes, sender: bytes, receiver: bytes, amount: int) -> None:
    _expect_account(client, "sender", wire, sender)
    _expect_account(client, "receiver", wire, receiver)
    _expect_u64(client, "amountW0", wire, amount & ((1 << 64) - 1))
    _expect_u64(client, "amountW1", wire, amount >> 64)


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("senderLength", wire)
    except NearRpcError:
        print(f"near-json-ft-resolve-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonFtResolveInput (two AccountIds + quoted u128) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    sender = b"sender.test.near"
    receiver = b"receiver.test.near"
    amount = (1 << 127) + (1 << 64) + 7
    fields = [
        (b"sender_id", b'"sender.test.near"'),
        (b"receiver_id", b'"receiver.test.near"'),
        (b"amount", f'"{amount}"'.encode()),
    ]
    for order in itertools.permutations(fields):
        _expect(client, _object(list(order)), sender, receiver, amount)
    print("near-json-ft-resolve-input: all six known-field permutations preserved both identities")

    equal_fields = [
        (b"receiver_id", b'"same.test.near"'),
        (b"amount", b'"0"'),
        (b"sender_id", b'"same.test.near"'),
    ]
    _expect(client, _object(equal_fields), b"same.test.near", b"same.test.near", 0)

    escaped_wire = _object([
        (b"amount", b'"' + _unicode_escape_ascii(str((1 << 64) + 1).encode()) + b'"'),
        (b"sender_id", b'"s\\u0065nder.test.near"'),
        (b"receiver_id", b'"r\\u0065ceiver.test.near"'),
    ])
    _expect(client, escaped_wire, sender, receiver, (1 << 64) + 1)

    max_account = b"a" * 64
    max_amount = (1 << 128) - 1
    max_wire = _object([
        (b"sender_id", b'"' + b"\\u0061" * 64 + b'"'),
        (b"receiver_id", b'"' + b"\\u0061" * 64 + b'"'),
        (b"amount", b'"' + _unicode_escape_ascii(str(max_amount).encode()) + b'"'),
    ], b" " * 32)
    if len(max_wire) != 1079:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 1079")
    _expect(client, max_wire, max_account, max_account, max_amount)

    invalid = [
        (b"{}", "missing all fields"),
        (_object(fields[1:]), "missing sender"),
        (_object([fields[0], fields[2]]), "missing receiver"),
        (_object(fields[:2]), "missing amount"),
        (_object(fields + [fields[0]]), "duplicate sender"),
        (_object(fields + [fields[1]]), "duplicate receiver"),
        (_object(fields + [fields[2]]), "duplicate amount"),
        (_object(fields + [(b"memo", b"null")]), "unknown field"),
        (_object([(b"s\\u0065nder_id", fields[0][1]), fields[1], fields[2]]), "escaped key"),
        (_object([(b"sender_id", b"1"), fields[1], fields[2]]), "sender wrong type"),
        (_object([fields[0], (b"receiver_id", b"1"), fields[2]]), "receiver wrong type"),
        (_object([fields[0], fields[1], (b"amount", b"1")]), "amount wrong type"),
        (_object([(b"sender_id", b'"a"'), fields[1], fields[2]]), "short sender"),
        (_object([fields[0], (b"receiver_id", b'"a"'), fields[2]]), "short receiver"),
        (_object([(b"sender_id", b'"' + b"a" * 65 + b'"'), fields[1], fields[2]]), "long sender"),
        (_object([fields[0], (b"receiver_id", b'"' + b"a" * 65 + b'"'), fields[2]]), "long receiver"),
        (_object([(b"sender_id", b'"Alice.near"'), fields[1], fields[2]]), "invalid sender syntax"),
        (_object([fields[0], (b"receiver_id", b'"bad..near"'), fields[2]]), "invalid receiver syntax"),
        (_object([(b"sender_id", b'"bad\\ud83d"'), fields[1], fields[2]]), "invalid sender escape"),
        (_object([fields[0], fields[1], (b"amount", b'""')]), "empty amount"),
        (_object([fields[0], fields[1], (b"amount", b'"+1"')]), "signed amount"),
        (_object([fields[0], fields[1], (b"amount", b'"01"')]), "leading-zero amount"),
        (_object([fields[0], fields[1], (b"amount", b'"340282366920938463463374607431768211456"')]), "amount overflow"),
        (_object(fields) + b"0", "trailing token after fully decoded values"),
        (b" " * 33 + _object(fields), "structural whitespace above 32"),
        (max_wire + b"0", "wire above exact 1079 bound"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)

    # A late failure after both AccountIds and amount were decoded must not contaminate the next
    # invocation's short active frames; all inactive words are checked by _expect_account.
    short_wire = _object([
        (b"amount", b'"9"'), (b"receiver_id", b'"bb"'), (b"sender_id", b'"aa"')])
    _expect(client, short_wire, b"aa", b"bb", 9)

    committed = client.call("commitAmountHigh", _object(fields))
    if NearClient.success_value_bytes(committed) != NearClient.encode_u64_le(amount >> 64):
        raise AssertionError("mutating resolver parser returned the wrong amount high limb")
    if client.view_u64("get") != amount >> 64:
        raise AssertionError("mutating resolver parser did not persist the amount high limb")
    client.call("commitAmountHigh", _object(fields) + b"0", expect_success=False)
    if client.view_u64("get") != amount >> 64:
        raise AssertionError("failed resolver argument parse changed state")

    print("near-json-ft-resolve-input: bounds, malformed matrix, inactive zeros, and rollback ok")
    print("suite NearJsonFtResolveInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-ft-resolve-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
