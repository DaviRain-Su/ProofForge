#!/usr/bin/env python3
"""Bounded one-field AccountId JSON object input scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-account-input: missing env {name}")
    return value


def _expect(client: NearClient, method: str, wire: bytes, value: int) -> None:
    got = client.view(method, wire)
    expected = NearClient.encode_u64_le(value)
    if got != expected:
        raise AssertionError(
            f"{method}({wire!r}): expected {expected.hex()}, got {got.hex()}"
        )


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("accountLength", wire)
    except NearRpcError:
        print(f"near-json-account-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def _wire(value: bytes) -> bytes:
    return b'{"account_id":"' + value + b'"}'


def _word(value: bytes, index: int) -> int:
    chunk = value[index * 8 : index * 8 + 8]
    return int.from_bytes(chunk.ljust(8, b"\0"), "little")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearJsonAccountInput (bounded object subset) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    short = b"aa"
    short_wire = _wire(short)
    _expect(client, "accountLength", short_wire, 2)
    _expect(client, "accountW0", short_wire, _word(short, 0))
    for index in range(1, 8):
        _expect(client, f"accountW{index}", short_wire, 0)
    print("near-json-account-input: minimum length and inactive zero limbs ok")

    maximum = b"abcdefgh01234567ijklmnop89abcdefqrstuvwx76543210yzabcdef01234567"
    if len(maximum) != 64:
        raise AssertionError(f"fixture maximum account is {len(maximum)}, expected 64")
    maximum_wire = _wire(maximum)
    _expect(client, "accountLength", maximum_wire, 64)
    for index in range(8):
        _expect(client, f"accountW{index}", maximum_wire, _word(maximum, index))
    print("near-json-account-input: asymmetric 64-byte carrier limb order ok")

    escaped = b'{"account_id":"a\\u0062\\u002ecd"}'
    decoded = b"ab.cd"
    _expect(client, "accountLength", escaped, len(decoded))
    _expect(client, "accountW0", escaped, _word(decoded, 0))
    escaped_upper_hex = b'{"account_id":"\\u006A\\u006b"}'
    _expect(client, "accountW0", escaped_upper_hex, _word(b"jk", 0))

    # Six token boundaries share an exact aggregate allowance of 32 JSON whitespace bytes.
    whitespace_32 = (
        b" " * 5 + b"{" + b"\t" * 5 + b'"account_id"' + b"\n" * 5
        + b":" + b"\r" * 5 + b'"aa"' + b" " * 5 + b"}" + b"\t" * 7
    )
    if sum(byte in b" \t\r\n" for byte in whitespace_32) != 32:
        raise AssertionError("whitespace boundary fixture is not exactly 32 bytes")
    _expect(client, "accountLength", whitespace_32, 2)

    fully_escaped = b"\\u0061" * 64
    max_wire = b" " * 32 + _wire(fully_escaped)
    if len(max_wire) != 433:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 433")
    _expect(client, "accountLength", max_wire, 64)
    for index in range(8):
        _expect(client, f"accountW{index}", max_wire, _word(b"a" * 64, index))
    print("near-json-account-input: escapes, whitespace, and exact 433-byte wire bound ok")

    invalid = [
        (b"", "empty input"),
        (_wire(b""), "empty account"),
        (_wire(b"a"), "one-byte account"),
        (_wire(b"a" * 65), "65-byte account"),
        (_wire(b"Aa"), "uppercase account"),
        (_wire(b"-aa"), "leading separator"),
        (_wire(b"aa_"), "trailing separator"),
        (_wire(b"aa.-bb"), "adjacent mixed separators"),
        (_wire(b"a/b"), "invalid account character"),
        (b'{"account_id":"a\\q"}', "unknown escape"),
        (b'{"account_id":"a\\"}', "dangling escape"),
        (b'{"account_id":"a\\u00xz"}', "invalid unicode hex"),
        (b'{"account_id":"a\\u0080"}', "non-ASCII unicode escape"),
        (b'{"account_id":"a\\ud800"}', "surrogate escape"),
        (b'{"account_id":"a\x01b"}', "raw control"),
        (b'{"account_id":"a\xc3\xa9"}', "raw non-ASCII UTF-8"),
        (b'{"account_id":"\xffa"}', "invalid UTF-8"),
        (b"{}", "missing field"),
        (b'{"other":"aa"}', "unknown field"),
        (b'{"account\\u005fid":"aa"}', "escaped key spelling"),
        (b'{"account_id":7}', "wrong value type"),
        (b'{"account_id":"aa","account_id":"bb"}', "duplicate field"),
        (b'{"account_id":"aa","other":0}', "unknown extra field"),
        (b'{"account_id":"aa"}0', "trailing token"),
        (b" " * 33 + _wire(b"aa"), "whitespace above 32"),
        (b"x" * 434, "wire above 433"),
    ]
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    print("near-json-account-input: malformed object/string/account matrix fail-closed ok")
    print("suite NearJsonAccountInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-account-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
