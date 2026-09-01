#!/usr/bin/env python3
"""Optional bounded UTF-8 memo JSON object scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-memo-input: missing env {name}")
    return value


def _wire(value: bytes) -> bytes:
    return b'{"memo":"' + value + b'"}'


def _expect_u64(client: NearClient, method: str, wire: bytes, value: int) -> None:
    got = client.view(method, wire)
    expected = NearClient.encode_u64_le(value)
    if got != expected:
        raise AssertionError(f"{method}({wire!r}): expected {expected.hex()}, got {got.hex()}")


def _expect(client: NearClient, wire: bytes, present: int, decoded: bytes) -> None:
    padded = decoded.ljust(16, b"\0")
    _expect_u64(client, "memoPresent", wire, present)
    _expect_u64(client, "memoLength", wire, len(decoded))
    _expect_u64(client, "memoW0", wire, int.from_bytes(padded[:8], "little"))
    _expect_u64(client, "memoW1", wire, int.from_bytes(padded[8:], "little"))


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("memoPresent", wire)
    except NearRpcError:
        print(f"near-json-memo-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonMemoInput (optional bounded UTF-8 subset) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    _expect(client, b"{}", 0, b"")
    _expect(client, b'{"memo":null}', 0, b"")
    _expect(client, _wire(b""), 1, b"")
    _expect(client, _wire(b"a\\\"b\\\\c\\/d"), 1, b'a"b\\c/d')
    _expect(client, _wire(b"\\b\\f\\n\\r\\t\\u0000"), 1, b"\x08\x0c\x0a\x0d\x09\x00")
    _expect(client, _wire("é雪".encode()), 1, "é雪".encode())
    _expect(client, _wire(b"\\u00e9\\u96ea"), 1, "é雪".encode())
    _expect(client, _wire(b"\\ud83d\\ude00"), 1, "😀".encode())
    _expect(client, _wire(b"\\udbff\\udfff"), 1, "\U0010ffff".encode())
    _expect(client, _wire(b"\x7f"), 1, b"\x7f")

    structural_ws_32 = (
        b" " * 5 + b"{" + b"\t" * 5 + b'"memo"' + b"\n" * 5 + b":"
        + b"\r" * 5 + b'"' + b" " * 16 + b'"' + b" " * 5 + b"}" + b"\t" * 7
    )
    if len(structural_ws_32) != 59:
        raise AssertionError("whitespace fixture geometry drift")
    _expect(client, structural_ws_32, 1, b" " * 16)
    max_wire = b" " * 32 + _wire(b"\\u0061" * 16)
    if len(max_wire) != 139:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 139")
    _expect(client, max_wire, 1, b"a" * 16)
    print("near-json-memo-input: None/Some, UTF-8, escapes, inactive zero, and bounds ok")

    result = client.call("commitLength", _wire("é雪".encode()))
    if NearClient.success_value_bytes(result) != NearClient.encode_u64_le(5):
        raise AssertionError("mutating memo wrapper returned wrong decoded byte length")
    if client.view_u64("get") != 5:
        raise AssertionError("mutating memo wrapper did not persist decoded byte length")

    invalid = [
        (b"", "empty input"),
        (b"null", "bare null"),
        (b'{"memo":1}', "wrong type"),
        (b'{"memo":false}', "wrong boolean type"),
        (b'{"other":null}', "unknown field"),
        (b'{"memo":null,"memo":null}', "duplicate field"),
        (b'{"memo":null,"other":0}', "unknown extra field"),
        (b'{"m\\u0065mo":null}', "escaped key"),
        (b'{"memo":null}0', "trailing token"),
        (_wire(b"a" * 17), "17 raw decoded bytes"),
        (_wire(b"\\u0061" * 17), "17 escaped decoded bytes"),
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
        (b" " * 33 + b"{}", "structural whitespace above 32"),
        (b"x" * 140, "wire above 139"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    print("near-json-memo-input: malformed grammar/UTF-8/capacity matrix fail-closed ok")
    print("suite NearJsonMemoInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-memo-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
