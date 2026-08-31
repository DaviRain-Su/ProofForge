#!/usr/bin/env python3
"""Static calls, entry policy, and authenticated self-callbacks against near-sandbox."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


RECEIVER = "receiver.test.near"
FT_OBSERVER = "observer.test.near"
JSON_RESULT = "json-result.test.near"


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
    observer_wasm = Path(_require("PF_NEAR_OBSERVER_WASM"))
    quoted_result_wasm = Path(_require("PF_NEAR_QUOTED_RESULT_WASM"))
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
    client.create_subaccount_with_key(FT_OBSERVER, 10**27)
    client.deploy_to(FT_OBSERVER, observer_wasm)
    client.create_subaccount_with_key(JSON_RESULT, 10**27)
    client.deploy_to(JSON_RESULT, quoted_result_wasm)
    if client.view_u64("get") != 0 or client.view_u64_on(RECEIVER, "get") != 0:
        raise AssertionError("caller and receiver must begin with marker zero")

    rejected_callback = client.call_on(
        RECEIVER,
        "callbackSuccess",
        NearClient.encode_u64_le(404),
        deposit=1,
        expect_success=False,
    )
    failure_text = repr(rejected_callback.get("status", {})) + repr(
        rejected_callback.get("receipts_outcome", [])
    )
    if "Method callbackSuccess is private" not in failure_text:
        raise AssertionError(
            "external paid callback call must fail at the private guard before non-payable, "
            f"got {failure_text}"
        )
    if client.view_u64_on(RECEIVER, "get") != 0:
        raise AssertionError("rejected external callback changed receiver state")
    print("near-promise: exact private guard won before non-payable on external paid callback")

    donation = client.call_on(
        RECEIVER,
        "recordValue",
        NearClient.encode_u64_le(303),
        deposit=17,
    )
    if NearClient.success_value_bytes(donation) != NearClient.encode_u64_le(303):
        raise AssertionError("donation-only payable entry lost its UInt64 result")
    if client.view_u64_on(RECEIVER, "get") != 303:
        raise AssertionError("donation-only payable entry did not commit receiver state")
    client.call_on(RECEIVER, "recordValue", NearClient.encode_u64_le(0))
    if client.view_u64_on(RECEIVER, "get") != 0:
        raise AssertionError("recordValue reset after payable scene failed")
    print("near-promise: explicit payable metadata accepted a body-independent donation")

    # The receiver-signed deployment/initialization can still have a delayed gas-refund receipt at
    # the first optimistic balance query. The intervening finalized callback call provides a stable
    # baseline before exact transfer deltas are measured.
    receiver_balance = client.view_account_balance(RECEIVER)
    _call_u64(client, "transferDetached", 501)
    next_receiver_balance = client.view_account_balance(RECEIVER)
    if next_receiver_balance - receiver_balance != (1 << 64) + 7:
        raise AssertionError(
            "detached native transfer did not deliver the exact u128 amount: "
            f"expected {(1 << 64) + 7}, got {next_receiver_balance - receiver_balance}"
        )
    if client.view_u64("get") != 501:
        raise AssertionError("detached native transfer did not commit caller state")
    print("near-promise: detached native transfer delivered exact low/high limbs")

    returned_transfer = _call_u64(client, "transferReturned", 502)
    if NearClient.success_value_bytes(returned_transfer) != b"":
        raise AssertionError("returned native transfer did not forward an empty receipt result")
    returned_receiver_balance = client.view_account_balance(RECEIVER)
    if returned_receiver_balance - next_receiver_balance != 11:
        raise AssertionError(
            "returned native transfer did not deliver exactly 11 yoctoNEAR: "
            f"got {returned_receiver_balance - next_receiver_balance}"
        )
    if client.view_u64("get") != 502:
        raise AssertionError("returned native transfer did not commit caller state")
    print("near-promise: returned native transfer forwarded its successful receipt")

    _call_u64(client, "transferTooMuch", 503, expect_success=False)
    if client.view_account_balance(RECEIVER) != returned_receiver_balance:
        raise AssertionError("insufficient native transfer unexpectedly changed receiver balance")
    if client.view_u64("get") != 502:
        raise AssertionError("insufficient native transfer did not roll back caller state")
    print("near-promise: insufficient native transfer failed synchronously and rolled back")

    padded_balance = client.view_account_balance(RECEIVER)
    _call_u64(client, "transferPaddedDetached", 504)
    padded_next_balance = client.view_account_balance(RECEIVER)
    if padded_next_balance - padded_balance != 19:
        raise AssertionError(
            "dynamic padded receiver did not use only its exact active AccountId bytes: "
            f"expected 19, got {padded_next_balance - padded_balance}"
        )
    if client.view_u64("get") != 504:
        raise AssertionError("dynamic padded detached transfer did not commit caller state")
    print("near-promise: inactive AccountId padding was excluded from the dynamic receiver")

    _call_u64(client, "transferSelfDetached", 506)
    if client.view_u64("get") != 506:
        raise AssertionError("zero-amount dynamic self transfer did not commit caller state")
    print("near-promise: complete dynamic current-account receiver created a detached receipt")

    dynamic_returned = client.call_on(
        client.account_id,
        "transferCallerReturned",
        NearClient.encode_u64_le(505),
        signer=RECEIVER,
    )
    if NearClient.success_value_bytes(dynamic_returned) != b"":
        raise AssertionError("dynamic predecessor transfer did not forward its empty receipt result")
    if client.view_u64("get") != 505:
        raise AssertionError("dynamic predecessor returned transfer did not commit caller state")
    print("near-promise: complete dynamic predecessor receiver produced a returned transfer receipt")

    amount_lo = 0xFEDCBA9876543210
    amount_hi = 0x123456789ABCDEF0
    _call_u64(client, "setFtAmountLo", amount_lo)
    _call_u64(client, "setFtAmountHi", amount_hi)

    def inspect_ft_message(message: str) -> None:
        parent_input = json.dumps(
            {"msg": message}, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")
        outcome = client.call("inspectFtOnTransfer", parent_input)
        observed = NearClient.success_value_bytes(outcome)
        expected_payload = json.dumps(
            {
                "sender_id": client.account_id,
                "amount": str((amount_hi << 64) | amount_lo),
                "msg": message,
            },
            ensure_ascii=False,
            separators=(",", ":"),
        ).encode("utf-8")
        if observed[:16] != bytes(16):
            raise AssertionError(
                f"weighted ft_on_transfer child observed nonzero attached deposit {observed[:16]!r}"
            )
        if observed[16:] != expected_payload:
            raise AssertionError(
                "weighted ft_on_transfer payload mismatch: "
                f"expected {expected_payload!r}, got {observed[16:]!r}"
            )
        if client.view_u64("get") != len(message.encode("utf-8")):
            raise AssertionError("returned weighted child did not persist the decoded message length")

    inspect_ft_message("")
    inspect_ft_message("nul:\x00 line:\n quote:\" slash:\\ emoji:😀")
    inspect_ft_message("a" * 64)
    print(
        "near-promise: weighted dynamic child received exact sender/u128/message JSON, "
        "zero deposit, and active receiver/message bytes"
    )

    missing_child = client.call(
        "inspectFtOnTransferMissing",
        b'{"msg":"async"}',
        expect_success=False,
    )
    missing_text = repr(missing_child.get("status", {})) + repr(
        missing_child.get("receipts_outcome", [])
    )
    if "missing.test.near" not in missing_text:
        raise AssertionError(f"missing weighted child failure was not observable: {missing_text}")
    if client.view_u64("get") != 5:
        raise AssertionError("asynchronous missing-account child rolled back caller state")
    print("near-promise: missing dynamic receiver failed asynchronously after caller commit")

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

    def check_quoted_result(
        method: str,
        expected_status: int,
        expected_valid: int,
        expected_lo: int,
        expected_hi: int,
        *,
        expect_success: bool = True,
    ) -> None:
        outcome = _call_u64(client, method, 700, expect_success=expect_success)
        actual_status = NearClient.success_value_bytes(outcome)
        if actual_status != NearClient.encode_u64_le(expected_status):
            raise AssertionError(
                f"{method} callback status expected {expected_status}, got {actual_status!r}"
            )
        actual = (
            client.view_u64("get"),
            client.view_u64("receivedDepositLo"),
            client.view_u64("receivedDepositHi"),
        )
        expected = (expected_valid, expected_lo, expected_hi)
        if actual != expected:
            raise AssertionError(f"{method} decoded {actual}, expected {expected}")

    mask = (1 << 64) - 1
    check_quoted_result("decodeJsonZero", 1, 1, 0, 0)
    check_quoted_result("decodeJsonHigh", 1, 1, 0, 1)
    check_quoted_result("decodeJsonMixed", 1, 1, 1, 1)
    check_quoted_result("decodeJsonMax", 1, 1, mask, mask)
    for method in (
        "decodeJsonLeadingZero",
        "decodeJsonPlus",
        "decodeJsonWhitespace",
        "decodeJsonUnquoted",
        "decodeJsonOverflow",
        "decodeJsonWrongType",
        "decodeJsonEmpty",
        "decodeJsonMalformedUtf8",
        "decodeJsonOversized",
    ):
        check_quoted_result(method, 1, 0, 0, 0)
    check_quoted_result("decodeJsonFailed", 2, 0, 0, 0, expect_success=False)
    check_quoted_result("decodeJsonMixed", 1, 1, 1, 1)
    print(
        "near-promise: strict quoted-u128 callback decoded full limbs and isolated stale results"
    )

    joined_success = _call_u64(client, "sendAndSuccess", 604)
    if NearClient.success_value_bytes(joined_success) != NearClient.encode_u64_le(456):
        raise AssertionError("joined callback did not forward the successful right result")
    if client.view_u64("get") != 80:
        raise AssertionError("joined callback did not commit its independent argument 80")
    if client.view_u64("receivedDepositLo") != 123 or client.view_u64(
        "receivedDepositHi"
    ) != 456:
        raise AssertionError("joined callback did not preserve successful left/right result order")
    print("near-promise: ordered join exposed two successful child results to one callback")

    joined_right_failure = _call_u64(
        client, "sendAndRightMissing", 605, expect_success=False
    )
    if NearClient.success_value_bytes(joined_right_failure) != NearClient.encode_u64_le(999):
        raise AssertionError("right-child failure did not forward the right-result fallback")
    if client.view_u64("get") != 81:
        raise AssertionError("right-child failure did not run and commit callback argument 81")
    if client.view_u64("receivedDepositLo") != 123 or client.view_u64(
        "receivedDepositHi"
    ) != 999:
        raise AssertionError("right-child failure changed left/right result ordering or fallback")
    print("near-promise: failed right child retained successful left result and ordered fallback")

    joined_left_failure = _call_u64(
        client, "sendAndLeftMissing", 606, expect_success=False
    )
    if NearClient.success_value_bytes(joined_left_failure) != NearClient.encode_u64_le(456):
        raise AssertionError("left-child failure did not forward the successful right result")
    if client.view_u64("get") != 82:
        raise AssertionError("left-child failure did not run and commit callback argument 82")
    if client.view_u64("receivedDepositLo") != 999 or client.view_u64(
        "receivedDepositHi"
    ) != 456:
        raise AssertionError("left-child failure short-circuited or reordered the right result")
    print("near-promise: failed left child did not short-circuit successful right result")

    _call_u64(client, "sendThenFail", 111, expect_success=False)
    if client.view_u64("get") != 82:
        raise AssertionError("caller panic did not roll back caller state")
    if client.view_u64_on(RECEIVER, "get") != 456:
        raise AssertionError("caller panic did not discard its staged outgoing receipt")
    print("near-promise: caller panic discarded staged receipt and rolled back")

    _call_u64(client, "sendTooMuch", 222, expect_success=False)
    if client.view_u64("get") != 82:
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
