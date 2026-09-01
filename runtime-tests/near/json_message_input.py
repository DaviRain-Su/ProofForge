#!/usr/bin/env python3
"""Required bounded UTF-8 message JSON object scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-message-input: missing env {name}")
    return value


def _wire(value: bytes) -> bytes:
    return b'{"msg":"' + value + b'"}'


def _expect_u64(client: NearClient, method: str, wire: bytes, value: int) -> None:
    got = client.view(method, wire)
    expected = NearClient.encode_u64_le(value)
    if got != expected:
        raise AssertionError(f"{method}({wire!r}): expected {expected.hex()}, got {got.hex()}")


def _expect(client: NearClient, wire: bytes, decoded: bytes) -> None:
    padded = decoded.ljust(64, b"\0")
    _expect_u64(client, "messageLength", wire, len(decoded))
    for index in range(8):
        _expect_u64(
            client,
            f"messageW{index}",
            wire,
            int.from_bytes(padded[index * 8 : (index + 1) * 8], "little"),
        )


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("messageLength", wire)
    except NearRpcError:
        print(f"near-json-message-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonMessageInput (required bounded UTF-8 subset) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    _expect(client, _wire(b""), b"")
    _expect(client, _wire(b"12345678Z"), b"12345678Z")
    _expect(client, _wire(b"abcdefghABCDEFGH"), b"abcdefghABCDEFGH")
    _expect(client, _wire(b"a\\\"b\\\\c\\/d"), b'a"b\\c/d')
    _expect(client, _wire(b"\\b\\f\\n\\r\\t\\u0000"), b"\x08\x0c\x0a\x0d\x09\x00")
    _expect(client, _wire("é雪".encode()), "é雪".encode())
    _expect(client, _wire(b"\\u00e9\\u96ea"), "é雪".encode())
    _expect(client, _wire(b"\\u00Ea\\u96EA"), "ê雪".encode())
    _expect(client, _wire(b"\\ud83d\\ude00"), "😀".encode())
    _expect(client, _wire(b"\\udbff\\udfff"), "\U0010ffff".encode())
    _expect(client, _wire(b"\x7f"), b"\x7f")
    _expect(client, _wire(b" " * 64), b" " * 64)
    _expect(client, _wire(b"a" * 60 + "😀".encode()), b"a" * 60 + "😀".encode())
    _expect(client, _wire(b"a" * 63 + b"\\u0000"), b"a" * 63 + b"\0")
    asymmetric = b"01234567ABCDEFGHijklmnopQRSTUVWXyzabcdefGHIJKLMNopqrstuv89uvwxyz"
    if len(asymmetric) != 64:
        raise AssertionError("asymmetric packed-word fixture geometry drift")
    _expect(client, _wire(asymmetric), asymmetric)
    _expect(client, _wire(b"a" * 63 + b"z"), b"a" * 63 + b"z")

    ws32 = b" " * 32 + _wire(b"")
    _expect(client, ws32, b"")
    max_wire = b" " * 32 + _wire(b"\\u0061" * 64)
    if len(max_wire) != 426:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 426")
    _expect(client, max_wire, b"a" * 64)
    print("near-json-message-input: UTF-8, escapes, packed limbs, inactive zero, and bounds ok")

    result = client.call("commitLength", _wire("é雪😀".encode()))
    if NearClient.success_value_bytes(result) != NearClient.encode_u64_le(9):
        raise AssertionError("mutating message wrapper returned wrong decoded byte length")
    if client.view_u64("get") != 9:
        raise AssertionError("mutating message wrapper did not persist decoded byte length")

    invalid = [
        (b"", "empty input"),
        (b"{}", "missing required field"),
        (b'{"msg":null}', "null required field"),
        (b'{"msg":1}', "wrong type"),
        (b'{"other":""}', "unknown field"),
        (b'{"msg":"","msg":""}', "duplicate field"),
        (b'{"msg":"","other":0}', "unknown extra field"),
        (b'{"m\\u0073g":""}', "escaped key"),
        (b'{"msg":""}0', "trailing token"),
        (_wire(b"a" * 65), "65 raw decoded bytes"),
        (_wire(b"\\u0061" * 65), "65 escaped decoded bytes"),
        (_wire(b"a" * 61 + "😀".encode()), "multibyte scalar crossing capacity"),
        (_wire(b"a" * 63 + b"\\ud83d\\ude00"), "surrogate pair crossing capacity"),
        (_wire(b"a\x01b"), "raw control"),
        (_wire(b"\\q"), "unknown short escape"),
        (_wire(b"\\u00xz"), "invalid hex"),
        (_wire(b"\\ud83d"), "isolated high surrogate"),
        (_wire(b"\\ud800\\ud800"), "high surrogate followed by high"),
        (_wire(b"\\ude00"), "isolated low surrogate"),
        (_wire(b"\\ude00\\ud83d"), "reversed surrogate pair"),
        (_wire(b"\\ud83d\\u0041"), "high surrogate with non-low"),
        (_wire(b"\xff"), "invalid UTF-8"),
        (_wire(b"\xc0\x80"), "overlong UTF-8"),
        (_wire(b"\xed\xa0\x80"), "raw UTF-8 surrogate"),
        (_wire(b"\xf4\x90\x80\x80"), "UTF-8 above Unicode maximum"),
        (_wire(b"\xe2\x82"), "truncated UTF-8"),
        (_wire(b"\x80"), "lone UTF-8 continuation"),
        (b" " * 33 + _wire(b""), "structural whitespace above 32"),
        (b"x" * 427, "wire above 426"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    print("near-json-message-input: malformed grammar/UTF-8/capacity matrix fail-closed ok")
    print("suite NearJsonMessageInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-message-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
