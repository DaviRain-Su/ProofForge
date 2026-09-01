#!/usr/bin/env python3
"""Bounded storage-deposit-shaped JSON argument scenes against near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-storage-deposit-input: missing env {name}")
    return value


def _expect_u64(client: NearClient, method: str, wire: bytes, expected: int) -> None:
    got = client.view(method, wire)
    encoded = NearClient.encode_u64_le(expected)
    if got != encoded:
        raise AssertionError(f"{method}: expected {encoded.hex()}, got {got.hex()} for {wire!r}")


def _expect(client: NearClient, wire: bytes, present: int, account: bytes, registration: int) -> None:
    frame = account.ljust(64, b"\0")
    _expect_u64(client, "inspectAccountPresent", wire, present)
    _expect_u64(client, "inspectAccountLength", wire, len(account))
    for index in range(8):
        _expect_u64(client, f"inspectAccountW{index}", wire,
                    int.from_bytes(frame[index * 8:(index + 1) * 8], "little"))
    _expect_u64(client, "inspectRegistrationOnly", wire, registration)


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("inspectAccountPresent", wire)
    except NearRpcError:
        print(f"near-json-storage-deposit-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    print("=== suite: NearJsonStorageDepositInput (optional account + bool) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    for wire in (b"{}", b'{"account_id":null}', b'{"registration_only":null}',
                 b'{"account_id":null,"registration_only":null}'):
        _expect(client, wire, 0, b"", 0)
    _expect(client, b'{"registration_only":false}', 0, b"", 1)
    _expect(client, b'{"registration_only":true}', 0, b"", 2)
    _expect(client, b'{"account_id":"alice.near"}', 1, b"alice.near", 0)
    _expect(client, b'{"account_id":"a\\u006cice.near","registration_only":true}',
            1, b"alice.near", 2)
    _expect(client, b'{"registration_only":false,"account_id":"aa"}', 1, b"aa", 1)

    max_account = b"a" * 64
    max_wire = (b" " * 32 + b'{"account_id":"' + b"\\u0061" * 64
                + b'","registration_only":false}')
    if len(max_wire) != 459:
        raise AssertionError(f"maximum wire is {len(max_wire)}, expected 459")
    _expect(client, max_wire, 1, max_account, 1)

    result = client.call("commitRegistrationOnly",
                         b'{"registration_only":true,"account_id":"zz"}')
    returned = NearClient.success_value_bytes(result)
    if returned != NearClient.encode_u64_le(2):
        raise AssertionError(f"mutating parser returned wrong boolean discriminant: {returned!r}")
    if client.view_u64("get") != 2:
        raise AssertionError("mutating parser did not persist boolean discriminant")

    invalid = [
        (b"", "empty input"), (b"null", "bare null"),
        (b'{"account_id":false}', "account wrong type"),
        (b'{"registration_only":0}', "boolean wrong type"),
        (b'{"registration_only":fals', "truncated false literal"),
        (b'{"registration_only":tru', "truncated true literal"),
        (b'{"registration_only":nul', "truncated null literal"),
        (b'{"account_id":nul', "truncated account null literal"),
        (b'{"account_id":"a"}', "one-byte account"),
        (b'{"account_id":"' + b"a" * 65 + b'"}', "65-byte account"),
        (b'{"account_id":"Alice.near"}', "invalid account syntax"),
        (b'{"account_id":null,"account_id":null}', "duplicate account"),
        (b'{"registration_only":null,"registration_only":true}', "duplicate boolean"),
        (b'{"unknown":null}', "unknown field"),
        (b'{"account_id":null,"unknown":0}', "unknown extra field"),
        (b'{"account\\u005fid":null}', "escaped account key"),
        (b'{"registration\\u005fonly":true}', "escaped boolean key"),
        (b'{"account_id":null}0', "trailing token"),
        (b'{"account_id":null,}', "trailing comma"),
        (b" " * 33 + b"{}", "whitespace above 32"),
        (b"x" * 460, "wire above 459"),
    ]
    before = client.view_u64("get")
    for wire, scene in invalid:
        _expect_failure(client, wire, scene)
    try:
        client.call("commitRegistrationOnly", b'{"registration_only":true,"unknown":0}')
    except NearRpcError:
        pass
    else:
        raise AssertionError("late mutating parse failure unexpectedly succeeded")
    if client.view_u64("get") != before:
        raise AssertionError("late mutating parse failure changed state")
    _expect(client, b"{}", 0, b"", 0)
    print("suite NearJsonStorageDepositInput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-storage-deposit-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
