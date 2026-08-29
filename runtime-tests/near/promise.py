#!/usr/bin/env python3
"""Detached static function-call Promise scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


RECEIVER = "receiver.test.near"


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-promise: missing env {name}")
    return value


def _call_u64(
    client: NearClient, method: str, value: int, *, expect_success: bool = True
) -> dict:
    return client.call(
        method, NearClient.encode_u64_le(value), expect_success=expect_success
    )


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearPromise (detached static function call) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    client.create_subaccount_with_key(RECEIVER, 10**27)
    client.deploy_to(RECEIVER, wasm)
    client.call_on(
        RECEIVER,
        "initialize",
        NearClient.encode_u64_le(0),
        signer=RECEIVER,
    )
    if client.view_u64("get") != 0 or client.view_u64_on(RECEIVER, "get") != 0:
        raise AssertionError("caller and receiver must begin with marker zero")

    _call_u64(client, "send", 77)
    if client.view_u64("get") != 77:
        raise AssertionError("detached sender did not commit its own state")
    if client.view_u64_on(RECEIVER, "get") != 77:
        raise AssertionError("detached receiver did not decode the exact UInt64 argument")
    if client.view_u64_on(RECEIVER, "receivedDepositLo") != 7:
        raise AssertionError("detached receiver did not observe u128 deposit low limb 7")
    if client.view_u64_on(RECEIVER, "receivedDepositHi") != 1:
        raise AssertionError("detached receiver did not observe u128 deposit high limb 1")
    print("near-promise: batch call delivered argument and LE u128 deposit exactly")

    _call_u64(client, "sendZero", 88)
    if client.view_u64_on(RECEIVER, "get") != 88:
        raise AssertionError("zero-deposit detached receipt did not execute")
    if client.view_u64_on(RECEIVER, "receivedDepositLo") != 0 or client.view_u64_on(
        RECEIVER, "receivedDepositHi"
    ) != 0:
        raise AssertionError("zero deposit did not arrive as two zero limbs")
    print("near-promise: zero-deposit detached call executed")

    _call_u64(client, "sendMissing", 99, expect_success=False)
    if client.view_u64("get") != 99:
        raise AssertionError("remote detached failure rolled back successful caller state")
    if client.view_u64_on(RECEIVER, "get") != 88:
        raise AssertionError("absent remote method unexpectedly changed receiver state")
    print("near-promise: remote detached failure left committed caller state intact")

    _call_u64(client, "sendThenFail", 111, expect_success=False)
    if client.view_u64("get") != 99:
        raise AssertionError("caller panic did not roll back caller state")
    if client.view_u64_on(RECEIVER, "get") != 88:
        raise AssertionError("caller panic did not discard its staged outgoing receipt")
    print("near-promise: caller panic discarded staged receipt and rolled back")

    _call_u64(client, "sendTooMuch", 222, expect_success=False)
    if client.view_u64("get") != 99:
        raise AssertionError("synchronous deposit failure did not roll back caller state")
    if client.view_u64_on(RECEIVER, "get") != 88:
        raise AssertionError("synchronous deposit failure emitted an outgoing receipt")
    print("near-promise: insufficient balance failed synchronously before commit")
    print("suite NearPromise: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-promise: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
