#!/usr/bin/env python3
"""Closed caller-registration economics scenes against local near-sandbox."""

from __future__ import annotations

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


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    contract = "reg.test.near"
    short = "a.test.near"
    long = "x" * (64 - len(".test.near")) + ".test.near"
    malformed = "bad.test.near"
    overflow = "overflow.test.near"
    zero_cost = "zero.test.near"

    for account in (contract, short, long, malformed, overflow, zero_cost):
        client.create_subaccount_with_key(account, 10**27)
    client.deploy_to(contract, wasm)
    per_byte = 10**19
    client.call_on(contract, "initialize", NearClient.encode_u64_le(per_byte), signer=contract)

    baseline_state = client.view_state_values(contract)
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

    before = client.view_account_balance(contract)
    duplicate_deposit = 10**22
    duplicate = _register(client, contract, short, duplicate_deposit)
    if _result_u64(duplicate) != short_delta:
        raise AssertionError("duplicate registration changed its state result")
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

    client.call_on(contract, "seedCallerMalformed8", b"", signer=malformed)
    malformed_before = client.view_state_values(contract)
    _register(client, contract, malformed, generous, success=False)
    if client.view_state_values(contract) != malformed_before:
        raise AssertionError("malformed present value rejection changed storage/state")

    client.deploy_to(overflow, wasm)
    client.call_on(
        overflow, "initialize", NearClient.encode_u64_le((1 << 64) - 1), signer=overflow
    )
    overflow_before = client.view_state_values(overflow)
    _register(client, overflow, short, 0, success=False)
    if client.view_state_values(overflow) != overflow_before or _key(short) in overflow_before:
        raise AssertionError("cost multiplication overflow did not roll back speculative write")

    client.deploy_to(zero_cost, wasm)
    client.call_on(zero_cost, "initialize", NearClient.encode_u64_le(0), signer=zero_cost)
    zero_before = client.view_state_values(zero_cost)
    _register(client, zero_cost, short, 0, success=False)
    if client.view_state_values(zero_cost) != zero_before:
        raise AssertionError("zero trusted cost was not rejected before storage effects")

    print("near-storage-registration: measured costs, refunds, and rollback boundaries ok")
    print("suite NearStorageRegistration: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage-registration: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
