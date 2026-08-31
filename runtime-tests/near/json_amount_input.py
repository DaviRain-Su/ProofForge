#!/usr/bin/env python3
"""Canonical one-field quoted-u128 amount JSON object input scenes."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-amount-input: missing env {name}")
    return value


def _wire(digits: bytes) -> bytes:
    return b'{"amount":"' + digits + b'"}'


def _expect(client: NearClient, method: str, wire: bytes, value: int) -> None:
    got = client.view(method, wire)
    expected = NearClient.encode_u64_le(value)
    if got != expected:
        raise AssertionError(
            f"{method}({wire!r}): expected {expected.hex()}, got {got.hex()}"
        )


def _expect_amount(client: NearClient, wire: bytes, value: int) -> None:
    mask = (1 << 64) - 1
    _expect(client, "amountW0", wire, value & mask)
    _expect(client, "amountW1", wire, value >> 64)


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("amountW0", wire)
    except NearRpcError:
        print(f"near-json-amount-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearJsonAmountInput (canonical amount object subset) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    accepted = [
        (0, _wire(b"0")),
        (1 << 64, _wire(str(1 << 64).encode())),
        ((1 << 64) + 1, _wire(str((1 << 64) + 1).encode())),
        ((0x123456789ABCDEF0 << 64) | 0x0FEDCBA987654321,
         _wire(str((0x123456789ABCDEF0 << 64) | 0x0FEDCBA987654321).encode())),
        ((1 << 128) - 1, _wire(str((1 << 128) - 1).encode())),
        (123, _wire(b"\\u0031\\u0032\\u0033")),
    ]
    for value, wire in accepted:
        _expect_amount(client, wire, value)

    whitespace_32 = (
        b" " * 5 + b"{" + b"\t" * 5 + b'"amount"' + b"\n" * 5
        + b":" + b"\r" * 5 + b'"1"' + b" " * 5 + b"}" + b"\t" * 7
    )
    if sum(byte in b" \t\r\n" for byte in whitespace_32) != 32:
        raise AssertionError("whitespace boundary fixture is not exactly 32 bytes")
    _expect_amount(client, whitespace_32, 1)

    max_digits = str((1 << 128) - 1).encode()
    max_escaped = b"".join(b"\\u00" + bytes(f"{digit:02x}", "ascii") for digit in max_digits)
    max_wire = b" " * 32 + _wire(max_escaped)
    if len(max_wire) != 279:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 279")
    _expect_amount(client, max_wire, (1 << 128) - 1)
    print("near-json-amount-input: limb order, escapes, and exact wire bound ok")

    commit_value = (7 << 64) | 9
    result = client.call("commitW1", _wire(str(commit_value).encode()))
    returned = NearClient.success_value_bytes(result)
    if returned != NearClient.encode_u64_le(7):
        raise AssertionError(f"commitW1 returned {returned!r}, expected high limb 7")
    if client.view_u64("get") != 7:
        raise AssertionError("mutating quoted-u128 input did not persist high limb")
    print("near-json-amount-input: mutating wrapper parsed and persisted both limbs ok")

    invalid = [
        (b"", "empty input"),
        (_wire(b""), "empty decimal"),
        (_wire(b"+1"), "plus sign"),
        (_wire(b"-1"), "minus sign"),
        (_wire(b"00"), "zero with leading zero"),
        (_wire(b"01"), "nonzero with leading zero"),
        (_wire(str(1 << 128).encode()), "max plus one"),
        (_wire(b"999999999999999999999999999999999999999"), "39-digit overflow"),
        (_wire(b"1" * 40), "40 decoded digits"),
        (_wire(b"1a"), "raw nondigit"),
        (_wire(b"\\u00xz"), "invalid unicode hex"),
        (_wire(b"\\ud800"), "surrogate escape"),
        (_wire(b"\\u002b"), "escaped plus"),
        (_wire(b"\\u0061"), "escaped nondigit"),
        (b"{}", "missing field"),
        (b'{"other":"1"}', "unknown field"),
        (b'{"amount":1}', "wrong value type"),
        (b'{"amount":"1","amount":"2"}', "duplicate field"),
        (b'{"amount":"1","other":0}', "unknown extra field"),
        (b'{"am\\u006funt":"1"}', "escaped key spelling"),
        (b'{"amount":"1"}0', "trailing token"),
        (b" " * 33 + _wire(b"1"), "whitespace above 32"),
        (b"x" * 280, "wire above 279"),
        (b'{"amount":"\xff"}', "invalid UTF-8"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    print("near-json-amount-input: malformed object/string/decimal matrix fail-closed ok")
    print("suite NearJsonAmountInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-amount-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
