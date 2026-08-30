#!/usr/bin/env python3
"""Static function-call and authenticated self-callback Promise edge against near-sandbox."""

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

    print("=== suite: NearPromise (static calls + self callback) ===")
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

    rejected_callback = client.call_on(
        RECEIVER,
        "callbackSuccess",
        NearClient.encode_u64_le(404),
        expect_success=False,
    )
    failure_text = repr(rejected_callback.get("status", {})) + repr(
        rejected_callback.get("receipts_outcome", [])
    )
    if "overflow" not in failure_text:
        raise AssertionError(
            "external callback call must fail at the self-call guard, "
            f"got {failure_text}"
        )
    if client.view_u64_on(RECEIVER, "get") != 0:
        raise AssertionError("rejected external callback changed receiver state")
    print("near-promise: external callback rejected by full AccountId self-call guard")

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

    returned = _call_u64(client, "sendReturned", 123)
    returned_value = NearClient.success_value_bytes(returned)
    expected_value = NearClient.encode_u64_le(123)
    if returned_value != expected_value:
        raise AssertionError(
            f"returned Promise SuccessValue expected {expected_value!r}, got {returned_value!r}"
        )
    if client.view_u64("get") != 123:
        raise AssertionError("returned Promise caller did not commit its own state")
    if client.view_u64_on(RECEIVER, "get") != 123:
        raise AssertionError("returned Promise receiver did not commit its state")
    print("near-promise: returned call forwarded exact 8-byte result and committed both receipts")

    _call_u64(client, "sendReturnedMissing", 144, expect_success=False)
    if client.view_u64("get") != 144:
        raise AssertionError("returned child failure rolled back the successful caller receipt")
    if client.view_u64_on(RECEIVER, "get") != 123:
        raise AssertionError("absent returned method unexpectedly changed receiver state")
    print("near-promise: returned remote failure propagated after caller state committed")

    then_success = _call_u64(client, "sendThenSuccess", 601)
    then_success_value = NearClient.success_value_bytes(then_success)
    if then_success_value != NearClient.encode_u64_le(123):
        raise AssertionError(
            f"successful callback expected decoded child value 123, got {then_success_value!r}"
        )
    if client.view_u64("get") != 77:
        raise AssertionError("successful callback did not preserve its separate argument 77")
    if client.view_u64_on(RECEIVER, "get") != 123:
        raise AssertionError("successful callback child did not return the expected value 123")
    print("near-promise: self callback observed exact successful child bytes and separate input")

    # The transaction's final value is successful, but the RPC result still contains the expected
    # failed child receipt, so the harness must permit a receipt-level failure here.
    then_failure = _call_u64(client, "sendThenMissing", 602, expect_success=False)
    if NearClient.success_value_bytes(then_failure) != NearClient.encode_u64_le(999):
        raise AssertionError("failed-child callback did not return decoder fallback 999")
    if client.view_u64("get") != 78:
        raise AssertionError("failed child did not run the callback's status-2 branch")
    if client.view_u64_on(RECEIVER, "get") != 123:
        raise AssertionError("missing child method unexpectedly changed receiver state")
    print("near-promise: failed child still ran callback with status 2 and no bytes")

    then_oversized = _call_u64(client, "sendThenOversized", 603)
    if NearClient.success_value_bytes(then_oversized) != NearClient.encode_u64_le(999):
        raise AssertionError("oversized-result callback did not return decoder fallback 999")
    if client.view_u64("get") != 79:
        raise AssertionError("callback did not observe successful length 8 as oversized for bound 4")
    if client.view_u64_on(RECEIVER, "get") != 456:
        raise AssertionError("oversized-result child did not execute with value 456")
    print("near-promise: bounded callback kept length 8/fits false without truncation")

    _call_u64(client, "sendThenFail", 111, expect_success=False)
    if client.view_u64("get") != 79:
        raise AssertionError("caller panic did not roll back caller state")
    if client.view_u64_on(RECEIVER, "get") != 456:
        raise AssertionError("caller panic did not discard its staged outgoing receipt")
    print("near-promise: caller panic discarded staged receipt and rolled back")

    _call_u64(client, "sendTooMuch", 222, expect_success=False)
    if client.view_u64("get") != 79:
        raise AssertionError("synchronous deposit failure did not roll back caller state")
    if client.view_u64_on(RECEIVER, "get") != 456:
        raise AssertionError("synchronous deposit failure emitted an outgoing receipt")
    print("near-promise: insufficient balance failed synchronously before commit")
    print("suite NearPromise: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-promise: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
