#!/usr/bin/env python3
"""Closed caller-registration economics scenes against local near-sandbox."""

from __future__ import annotations

import json
import os
import struct
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-storage-registration: missing env {name}")
    return value


def _key(account: str) -> bytes:
    raw = account.encode()
    return b"BAL2" + struct.pack("<I", len(raw)) + raw


def _balance_args(account: str) -> bytes:
    return json.dumps({"account_id": account}, separators=(",", ":")).encode()


def _expect_storage_balance(
    client: NearClient, contract: str, account: str, total: int | None
) -> None:
    before = client.view_state_values(contract)
    got = client.view_on(contract, "storage_balance_of", _balance_args(account))
    expected = (
        b"null"
        if total is None
        else f'{{"total":"{total}","available":"0"}}'.encode("ascii")
    )
    if got != expected:
        raise AssertionError(
            f"storage_balance_of({account}): expected {expected!r}, got {got!r}"
        )
    if client.view_state_values(contract) != before:
        raise AssertionError("storage_balance_of changed contract state")


def _expect_storage_balance_failure(
    client: NearClient, contract: str, account: str, scene: str
) -> None:
    before = client.view_state_values(contract)
    try:
        client.view_on(contract, "storage_balance_of", _balance_args(account))
    except NearRpcError:
        if client.view_state_values(contract) != before:
            raise AssertionError(f"{scene}: failed view changed contract state")
        return
    raise AssertionError(f"{scene}: expected storage_balance_of failure")


def _expect_storage_bounds(client: NearClient, contract: str, per_byte: int) -> None:
    before = client.view_state_values(contract)
    got = client.view_on(contract, "storage_balance_bounds", b"")
    expected = (
        f'{{"min":"{66 * per_byte}","max":"{128 * per_byte}"}}'.encode("ascii")
    )
    if got != expected:
        raise AssertionError(f"storage_balance_bounds: expected {expected!r}, got {got!r}")
    if client.view_state_values(contract) != before:
        raise AssertionError("storage_balance_bounds changed contract state")


def _expect_storage_bounds_failure(
    client: NearClient, contract: str, wire: bytes, scene: str
) -> None:
    before = client.view_state_values(contract)
    try:
        client.view_on(contract, "storage_balance_bounds", wire)
    except NearRpcError:
        if client.view_state_values(contract) != before:
            raise AssertionError(f"{scene}: failed bounds view changed contract state")
        return
    raise AssertionError(f"{scene}: expected storage_balance_bounds failure")


def _result_u64(outcome: dict) -> int:
    raw = NearClient.success_value_bytes(outcome)
    if raw is None or len(raw) != 8:
        raise AssertionError(f"expected exact u64 success value, got {raw!r}")
    return NearClient.decode_u64_le(raw)


def _register(client: NearClient, contract: str, caller: str, deposit: int,
              *, success: bool = True) -> dict:
    return client.call_on(
        contract, "registerCaller", b"", signer=caller, deposit=deposit,
        expect_success=success,
    )


def _unregister(client: NearClient, contract: str, caller: str, deposit: int,
                *, success: bool = True) -> dict:
    return client.call_on(
        contract, "unregisterCaller", b"", signer=caller, deposit=deposit,
        expect_success=success,
    )


def _force_unregister(client: NearClient, contract: str, caller: str, force: int,
                      *, deposit: int = 1, success: bool = True) -> dict:
    return client.call_on(
        contract, "forceUnregisterCaller", NearClient.encode_u64_le(force),
        signer=caller, deposit=deposit, expect_success=success,
    )


def _assert_transfer_receipt(
    client: NearClient, outcome: dict, receiver: str, amount: int
) -> None:
    observed: list[object] = []
    for record in outcome.get("receipts_outcome", []):
        receipt_id = record.get("id")
        if not receipt_id:
            continue
        receipt = client.rpc_call("EXPERIMENTAL_receipt", {"receipt_id": receipt_id})
        observed.append(receipt)
        if receipt.get("receiver_id") != receiver:
            continue
        actions = receipt.get("receipt", {}).get("Action", {}).get("actions", [])
        if any(
            int(action.get("Transfer", {}).get("deposit", -1)) == amount
            for action in actions
            if isinstance(action, dict)
        ):
            status = record.get("outcome", {}).get("status", {})
            if not (isinstance(status, dict) and "SuccessValue" in status):
                raise AssertionError(f"refund transfer receipt failed: {status!r}")
            return
    raise AssertionError(
        f"missing exact transfer receipt receiver={receiver} amount={amount}: {observed!r}"
    )


def _assert_exact_reclaim(
    client: NearClient, contract: str, caller: str, expected_delta: int, per_byte: int
) -> None:
    key = _key(caller)
    state_before = client.view_state_values(contract)
    if state_before.get(key) != b"\0" * 16:
        raise AssertionError(f"{caller} was not present exact zero before unregister")
    balance_before = client.view_account_balance(caller)
    outcome = _unregister(client, contract, caller, 1)
    balance_after = client.view_account_balance(caller)
    if _result_u64(outcome) != 1:
        raise AssertionError(f"{caller} unregister did not return true")
    reclaimed = client.view_u64_on(contract, "lastDelta")
    expected_cost = reclaimed * per_byte
    if reclaimed != expected_delta:
        raise AssertionError(
            f"{caller} reclaim delta {reclaimed} != registration delta {expected_delta}"
        )
    _assert_transfer_receipt(client, outcome, caller, expected_cost + 1)
    if balance_after <= balance_before:
        raise AssertionError(
            f"{caller} did not observe positive net balance after its successful exact refund"
        )
    if key in client.view_state_values(contract):
        raise AssertionError(f"{caller} canonical registration key survived unregister")


def _assert_force_reclaim(
    client: NearClient, contract: str, caller: str, expected_delta: int, per_byte: int
) -> None:
    balance_before = client.view_account_balance(caller)
    outcome = _force_unregister(client, contract, caller, 1)
    balance_after = client.view_account_balance(caller)
    if _result_u64(outcome) != 1:
        raise AssertionError("force unregister did not return true")
    reclaimed = client.view_u64_on(contract, "lastDelta")
    if reclaimed != expected_delta:
        raise AssertionError(f"force reclaim {reclaimed} != insertion {expected_delta}")
    _assert_transfer_receipt(client, outcome, caller, reclaimed * per_byte + 1)
    if balance_after <= balance_before or _key(caller) in client.view_state_values(contract):
        raise AssertionError("force unregister did not deliver refund and remove balance key")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    contract = "reg.test.near"
    short = "a.test.near"
    long = "x" * (64 - len(".test.near")) + ".test.near"
    malformed = "bad.test.near"
    nonzero = "one.test.near"
    forced = "force.test.near"
    overflow = "overflow.test.near"
    add_overflow = "y" * 11 + ".test.near"
    zero_cost = "zero.test.near"

    for account in (
        contract, short, long, malformed, nonzero, forced, overflow, add_overflow, zero_cost
    ):
        client.create_subaccount_with_key(account, 10**27)
    client.deploy_to(contract, wasm)
    per_byte = 10**19
    client.call_on(contract, "initialize", NearClient.encode_u64_le(per_byte), signer=contract)

    baseline_state = client.view_state_values(contract)
    _expect_storage_bounds(client, contract, per_byte)
    _expect_storage_bounds_failure(
        client, contract, b"{}", "nonempty no-argument bounds input"
    )
    _expect_storage_bounds_failure(
        client, contract, b"not-json", "arbitrary nonempty bounds input"
    )
    _expect_storage_balance(client, contract, short, None)
    _register(client, contract, short, 0, success=False)
    if client.view_state_values(contract) != baseline_state:
        raise AssertionError("insufficient deposit left speculative key or state residue")
    _register(client, contract, short, 1, success=False)
    if client.view_state_values(contract) != baseline_state:
        raise AssertionError("attached insufficient deposit left speculative state residue")
    # nearcore execution rebates make failed-call account-balance deltas path/gas dependent; both
    # failures are receipt panics, so attached deposit refund follows nearcore atomic rollback.

    generous = 10**24
    before = client.view_account_balance(contract)
    short_outcome = _register(client, contract, short, generous)
    short_delta = _result_u64(short_outcome)
    after = client.view_account_balance(contract)
    short_cost = short_delta * per_byte
    if short_delta <= 0 or not (short_cost <= after - before < generous):
        raise AssertionError(
            f"short registration gain {after-before} did not retain cost and refund excess"
        )
    if (
        client.view_u64_on(contract, "lastCostW0")
        != (short_cost & ((1 << 64) - 1))
        or client.view_u64_on(contract, "lastCostW1") != (short_cost >> 64)
    ):
        raise AssertionError("short registration stored the wrong measured u128 cost")
    state = client.view_state_values(contract)
    if state.get(_key(short)) != b"\0" * 16:
        raise AssertionError("registration did not store a present exact-zero NearToken")
    _expect_storage_balance(client, contract, short, short_cost)
    escaped_before = client.view_state_values(contract)
    escaped = client.view_on(
        contract, "storage_balance_of", b'{"account_id":"\\u0061.test.near"}'
    )
    escaped_expected = f'{{"total":"{short_cost}","available":"0"}}'.encode("ascii")
    if escaped != escaped_expected:
        raise AssertionError(
            f"escaped AccountId query: expected {escaped_expected!r}, got {escaped!r}"
        )
    if client.view_state_values(contract) != escaped_before:
        raise AssertionError("escaped AccountId storage-balance query changed state")

    before = client.view_account_balance(contract)
    duplicate_deposit = 10**22
    duplicate = _register(client, contract, short, duplicate_deposit)
    duplicate_result = _result_u64(duplicate)
    if duplicate_result != short_delta:
        raise AssertionError(
            f"duplicate registration changed its state result: {duplicate_result} != {short_delta}"
        )
    if client.view_account_balance(contract) - before >= duplicate_deposit:
        raise AssertionError("duplicate registration retained its attached deposit")
    _register(client, contract, short, 0)

    before = client.view_account_balance(contract)
    long_outcome = _register(client, contract, long, generous)
    long_delta = _result_u64(long_outcome)
    long_cost = long_delta * per_byte
    if not (long_cost <= client.view_account_balance(contract) - before < generous):
        raise AssertionError("long registration did not retain its own measured cost")
    if long_delta - short_delta != len(long) - len(short):
        raise AssertionError(
            f"caller-length delta mismatch: short={short_delta}, long={long_delta}"
        )
    if client.view_state_values(contract).get(_key(long)) != b"\0" * 16:
        raise AssertionError("max-length caller key was not exact active AccountId bytes")
    _expect_storage_balance(client, contract, long, long_cost)

    # The strict guard runs before lookup/removal. Both rejected deposits leave the complete
    # contract state untouched, including the present-zero key and diagnostic envelope.
    for caller in (short, long):
        for deposit in (0, 2):
            guarded = client.view_state_values(contract)
            _unregister(client, contract, caller, deposit, success=False)
            if client.view_state_values(contract) != guarded:
                raise AssertionError("failed one-yocto guard changed registration state")

    # Reverse insertion order so each live measured removal exactly reverses its corresponding
    # variable-length registration geometry, without assuming a fixed AccountId storage charge.
    _assert_exact_reclaim(client, contract, long, long_delta, per_byte)
    _assert_exact_reclaim(client, contract, short, short_delta, per_byte)
    _expect_storage_bounds(client, contract, per_byte)
    _expect_storage_balance(client, contract, short, None)
    missing_before = client.view_state_values(contract)
    if _result_u64(_unregister(client, contract, short, 1)) != 0:
        raise AssertionError("missing unregister did not return false")
    if _key(short) in client.view_state_values(contract):
        raise AssertionError("missing unregister recreated the registration key")
    # Like near-sdk-rs, the strict attached yocto is retained on the missing/false path. The
    # ProofForge state envelope may be rewritten to carry the false result, but the map is untouched.
    if set(client.view_state_values(contract)) != set(missing_before):
        raise AssertionError("missing unregister changed the storage key set")

    # The force path uses the same BAL2 registration/balance key and lossless supply state. A
    # non-force request rejects a positive balance before removal; force burns mixed and max u128.
    force_guard_before = client.view_state_values(contract)
    for deposit in (0, 2):
        _force_unregister(client, contract, forced, 1, deposit=deposit, success=False)
        if client.view_state_values(contract) != force_guard_before:
            raise AssertionError("force unregister one-yocto guard changed state")
    _force_unregister(client, contract, forced, 2, success=False)
    if client.view_state_values(contract) != force_guard_before:
        raise AssertionError("force unregister accepted a non-Boolean force flag")

    forced_delta = _result_u64(_register(client, contract, forced, generous))
    client.call_on(contract, "fixtureSeedCallerMixedSupply", b"", signer=forced)
    positive_before = client.view_state_values(contract)
    _force_unregister(client, contract, forced, 0, success=False)
    if client.view_state_values(contract) != positive_before:
        raise AssertionError("non-force positive balance rejection changed map/supply")
    _assert_force_reclaim(client, contract, forced, forced_delta, per_byte)
    if client.view_u64_on(contract, "totalSupplyW0") != 0 or client.view_u64_on(
        contract, "totalSupplyW1"
    ) != 0:
        raise AssertionError("mixed force burn did not reduce both supply limbs to zero")

    max_delta = _result_u64(_register(client, contract, forced, generous))
    client.call_on(contract, "fixtureSeedCallerMaxSupply", b"", signer=forced)
    _assert_force_reclaim(client, contract, forced, max_delta, per_byte)
    if client.view_u64_on(contract, "totalSupplyW0") != 0 or client.view_u64_on(
        contract, "totalSupplyW1"
    ) != 0:
        raise AssertionError("maximum force burn did not preserve conservation")

    zero_force_delta = _result_u64(_register(client, contract, forced, generous))
    _assert_force_reclaim(client, contract, forced, zero_force_delta, per_byte)
    if client.view_u64_on(contract, "totalSupplyW0") != 0 or client.view_u64_on(
        contract, "totalSupplyW1"
    ) != 0:
        raise AssertionError("zero-balance force changed total supply")
    force_missing_before = client.view_state_values(contract)
    if _result_u64(_force_unregister(client, contract, forced, 1)) != 0:
        raise AssertionError("missing force unregister did not return false")
    if set(client.view_state_values(contract)) != set(force_missing_before):
        raise AssertionError("missing force unregister changed the storage key set")

    client.call_on(contract, "seedCallerOne", b"", signer=forced)
    underflow_before = client.view_state_values(contract)
    _force_unregister(client, contract, forced, 1, success=False)
    if client.view_state_values(contract) != underflow_before:
        raise AssertionError("supply underflow was not rejected before removal")

    client.call_on(contract, "seedCallerMalformed8", b"", signer=malformed)
    malformed_before = client.view_state_values(contract)
    _expect_storage_balance_failure(
        client, contract, malformed, "malformed registration query"
    )
    _force_unregister(client, contract, malformed, 1, success=False)
    if client.view_state_values(contract) != malformed_before:
        raise AssertionError("malformed unregister rejection changed storage/state")

    client.call_on(contract, "seedCallerOne", b"", signer=nonzero)
    nonzero_before = client.view_state_values(contract)
    _unregister(client, contract, nonzero, 1, success=False)
    if client.view_state_values(contract) != nonzero_before:
        raise AssertionError("nonzero unregister rejection changed storage/state")

    client.deploy_to(overflow, wasm)
    client.call_on(
        overflow, "initialize", NearClient.encode_u64_le((1 << 64) - 1), signer=overflow
    )
    client.call_on(overflow, "fixtureSetCostMax", b"", signer=overflow)
    client.call_on(overflow, "seedCallerZero", b"", signer=short)
    overflow_before = client.view_state_values(overflow)
    _expect_storage_bounds_failure(
        client, overflow, b"", "registration bounds multiply overflow"
    )
    _expect_storage_balance_failure(
        client, overflow, short, "registration-cost multiply overflow query"
    )
    _force_unregister(client, overflow, short, 1, success=False)
    if client.view_state_values(overflow) != overflow_before or _key(short) not in overflow_before:
        raise AssertionError("reclaim-cost overflow did not roll back speculative removal")

    client.deploy_to(add_overflow, wasm)
    client.call_on(
        add_overflow, "initialize", NearClient.encode_u64_le(1), signer=add_overflow
    )
    client.call_on(
        add_overflow, "fixtureSetCostAddOverflow", b"", signer=add_overflow
    )
    client.call_on(add_overflow, "seedCallerZero", b"", signer=add_overflow)
    add_overflow_before = client.view_state_values(add_overflow)
    _force_unregister(client, add_overflow, add_overflow, 1, success=False)
    if client.view_state_values(add_overflow) != add_overflow_before:
        raise AssertionError("refund addition overflow did not roll back speculative removal")

    client.deploy_to(zero_cost, wasm)
    client.call_on(zero_cost, "initialize", NearClient.encode_u64_le(0), signer=zero_cost)
    zero_before = client.view_state_values(zero_cost)
    _expect_storage_bounds_failure(client, zero_cost, b"", "zero trusted cost bounds")
    _register(client, zero_cost, short, 0, success=False)
    if client.view_state_values(zero_cost) != zero_before:
        raise AssertionError("zero trusted cost was not rejected before storage effects")

    print("near-storage-registration: register/unregister costs, refunds, and rollback boundaries ok")
    print("suite NearStorageRegistration: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage-registration: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
