#!/usr/bin/env python3
"""Combined bounded transfer-shaped JSON argument scenes against near-sandbox."""

from __future__ import annotations

import itertools
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-ft-transfer-input: missing env {name}")
    return value


def _object(fields: list[tuple[bytes, bytes]], prefix: bytes = b"") -> bytes:
    return prefix + b"{" + b",".join(b'"' + k + b'":' + v for k, v in fields) + b"}"


def _unicode_escape_ascii(value: bytes) -> bytes:
    return b"".join(f"\\u{byte:04x}".encode() for byte in value)


def _expect_u64(client: NearClient, method: str, wire: bytes, expected: int) -> None:
    got = client.view(method, wire)
    encoded = NearClient.encode_u64_le(expected)
    if got != encoded:
        raise AssertionError(f"{method}: expected {encoded.hex()}, got {got.hex()} for {wire!r}")


def _expect(client: NearClient, wire: bytes, receiver: bytes, amount: int,
            memo_present: int, memo: bytes) -> None:
    _expect_u64(client, "inspectReceiverLength", wire, len(receiver))
    receiver_frame = receiver.ljust(64, b"\0")
    for index in range(8):
        _expect_u64(client, f"inspectReceiverW{index}", wire,
                    int.from_bytes(receiver_frame[index * 8:(index + 1) * 8], "little"))
    _expect_u64(client, "inspectAmountW0", wire, amount & ((1 << 64) - 1))
    _expect_u64(client, "inspectAmountW1", wire, amount >> 64)
    _expect_u64(client, "inspectMemoPresent", wire, memo_present)
    _expect_u64(client, "inspectMemoLength", wire, len(memo))
    memo_frame = memo.ljust(16, b"\0")
    _expect_u64(client, "inspectMemoW0", wire, int.from_bytes(memo_frame[:8], "little"))
    _expect_u64(client, "inspectMemoW1", wire, int.from_bytes(memo_frame[8:], "little"))


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("inspectReceiverLength", wire)
    except NearRpcError:
        print(f"near-json-ft-transfer-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonFtTransferInput (combined bounded field loop) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    receiver = b"alice.near"
    amount = (1 << 128) - 1
    memo = "😀".encode()
    fields = [(b"receiver_id", b'"alice.near"'),
              (b"amount", b'"340282366920938463463374607431768211455"'),
              (b"memo", b'"\\ud83d\\ude00"')]
    for order in itertools.permutations(fields):
        _expect(client, _object(list(order)), receiver, amount, 1, memo)

    required = fields[:2]
    for order in itertools.permutations(required):
        _expect(client, _object(list(order)), receiver, amount, 0, b"")
    _expect(client, _object(required + [(b"memo", b"null")]), receiver, amount, 0, b"")
    _expect(client, _object([(b"memo", b'""')] + required), receiver, amount, 1, b"")

    escaped = _object([
        (b"amount", b'"' + _unicode_escape_ascii(str(1 << 64).encode()) + b'"'),
        (b"memo", b'"\\u00e9\\u96ea"'),
        (b"receiver_id", b'"a\\u006cice.near"'),
    ])
    print("near-json-ft-transfer-input: checking escaped combined values")
    _expect(client, escaped, receiver, 1 << 64, 1, "é雪".encode())

    max_receiver = b"a" * 64
    max_wire = _object([
        (b"receiver_id", b'"' + b"\\u0061" * 64 + b'"'),
        (b"amount", b'"' + _unicode_escape_ascii(b"340282366920938463463374607431768211455") + b'"'),
        (b"memo", b'"' + b"\\u0061" * 16 + b'"'),
    ], b" " * 32)
    if len(max_wire) != 786:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 786")
    print("near-json-ft-transfer-input: checking exact maximum wire")
    _expect(client, max_wire, max_receiver, amount, 1, b"a" * 16)

    result = client.call("commitMemoLength", _object(fields))
    returned = NearClient.success_value_bytes(result)
    if returned != NearClient.encode_u64_le(len(memo)):
        raise AssertionError(f"mutating combined wrapper returned wrong committed state: {returned.hex()}")
    if client.view_u64("get") != len(memo):
        raise AssertionError("mutating combined wrapper did not persist memo byte length")

    invalid = [
        (b"{}", "missing required fields"),
        (_object([fields[0]]), "missing amount"),
        (_object([fields[1]]), "missing receiver"),
        (_object(required + [fields[0]]), "duplicate receiver"),
        (_object(required + [fields[1]]), "duplicate amount"),
        (_object(required + [fields[2], fields[2]]), "duplicate memo"),
        (_object(required + [(b"other", b"0")]), "unknown field"),
        (_object([(b"r\\u0065ceiver_id", b'"alice.near"'), fields[1]]), "escaped key"),
        (_object([(b"receiver_id", b"1"), fields[1]]), "receiver wrong type"),
        (_object([fields[0], (b"amount", b"1")]), "amount wrong type"),
        (_object(required + [(b"memo", b"1")]), "memo wrong type"),
        (_object([(b"receiver_id", b'"a"'), fields[1]]), "short receiver"),
        (_object([(b"receiver_id", b'"' + b"a" * 65 + b'"'), fields[1]]), "long receiver"),
        (_object([(b"receiver_id", b'"Alice.near"'), fields[1]]), "invalid receiver syntax"),
        (_object([fields[0], (b"amount", b'"340282366920938463463374607431768211456"')]), "amount overflow"),
        (_object([fields[0], (b"amount", b'"01"')]), "amount leading zero"),
        (_object(required + [(b"memo", b'"' + b"a" * 17 + b'"')]), "memo above 16 bytes"),
        (_object(required + [(b"memo", b'"\\ud83d"')]), "memo isolated surrogate"),
        (_object(required + [(b"memo", b'"\xff"')]), "memo malformed UTF-8"),
        (_object(required) + b"0", "trailing token"),
        (b" " * 33 + _object(required), "structural whitespace above 32"),
        (_object(required)[:-1] + b",}", "trailing comma"),
        (b"x" * 787, "wire above 786"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    print("near-json-ft-transfer-input: permutations, limbs, bounds, and malformed matrix ok")
    print("suite NearJsonFtTransferInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-ft-transfer-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
