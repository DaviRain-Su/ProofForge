#!/usr/bin/env python3
"""Closed internal fungible-ledger scenes against local near-sandbox."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


PREFIX = b"BAL2"
MAX_U128 = (1 << 128) - 1
_MISSING = object()


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-ledger: missing env {name}")
    return value


def _key(account_id: str) -> bytes:
    raw = account_id.encode("utf-8")
    return PREFIX + len(raw).to_bytes(4, "little") + raw


def _call(client: NearClient, method: str, *, signer: str | None = None) -> dict:
    return client.call_on(client.account_id, method, b"", signer=signer)


def _fail_unchanged(
    client: NearClient, method: str, scene: str, *, signer: str | None = None
) -> None:
    before = client.view_state_values()
    client.call_on(
        client.account_id, method, b"", signer=signer, expect_success=False
    )
    after = client.view_state_values()
    if after != before:
        raise AssertionError(f"{scene}: rejected receipt changed durable state")


def _view(client: NearClient, method: str) -> int:
    return client.view_u64(method)


def _balance(state: dict[bytes, bytes], account_id: str) -> int | None:
    value = state.get(_key(account_id))
    return None if value is None else int.from_bytes(value, "little")


def _supply(client: NearClient) -> int:
    return _view(client, "supplyW0") | (_view(client, "supplyW1") << 64)


def _json_balance(client: NearClient, account: bytes) -> int:
    wire = b'{"account_id":"' + account + b'"}'
    raw = client.view("ft_balance_of", wire)
    if len(raw) < 3 or raw[:1] != b'"' or raw[-1:] != b'"':
        raise AssertionError(f"ft_balance_of returned non-quoted-u128 bytes: {raw!r}")
    return int(raw[1:-1])


def _json_balance_fails(client: NearClient, account: bytes, scene: str) -> None:
    wire = b'{"account_id":"' + account + b'"}'
    try:
        client.view("ft_balance_of", wire)
    except NearRpcError:
        return
    raise AssertionError(f"{scene}: malformed stored value did not fail the view")


def _json_supply(client: NearClient, wire: bytes = b"") -> int:
    raw = client.view("ft_total_supply", wire)
    if len(raw) < 3 or raw[:1] != b'"' or raw[-1:] != b'"':
        raise AssertionError(f"ft_total_supply returned non-quoted-u128 bytes: {raw!r}")
    value = int(raw[1:-1])
    if raw != f'"{value}"'.encode():
        raise AssertionError(f"ft_total_supply returned noncanonical decimal bytes: {raw!r}")
    return value


def _metadata_wire() -> bytes:
    return json.dumps(
        {
            "spec": "ft-1.0.0",
            "name": "ProofForge Token",
            "symbol": "PF",
            "icon": None,
            "reference": None,
            "reference_hash": None,
            "decimals": 18,
        },
        separators=(",", ":"),
    ).encode("utf-8")


def _storage_balance(client: NearClient, account_id: str) -> bytes:
    return client.view(
        "storage_balance_of",
        json.dumps({"account_id": account_id}, separators=(",", ":")).encode(),
    )


def _receipt_logs(response: dict) -> list[str]:
    return [
        log
        for receipt in response.get("receipts_outcome", ())
        for log in receipt.get("outcome", {}).get("logs", ())
    ]


def _assert_transfer_receipt(
    client: NearClient, outcome: dict, receiver: str, amount: int
) -> None:
    for record in outcome.get("receipts_outcome", ()):
        receipt_id = record.get("id")
        if not receipt_id:
            continue
        receipt = client.rpc_call("EXPERIMENTAL_receipt", {"receipt_id": receipt_id})
        if receipt.get("receiver_id") != receiver:
            continue
        actions = receipt.get("receipt", {}).get("Action", {}).get("actions", ())
        if any(
            isinstance(action, dict)
            and int(action.get("Transfer", {}).get("deposit", -1)) == amount
            for action in actions
        ):
            return
    raise AssertionError(f"missing refund transfer to {receiver} for {amount}")


def _ft_args(receiver: str, amount: int, memo: object = _MISSING) -> bytes:
    fields: dict[str, object] = {"receiver_id": receiver, "amount": str(amount)}
    if memo is not _MISSING:
        fields["memo"] = memo
    return json.dumps(fields, separators=(",", ":"), ensure_ascii=False).encode()


def _transfer_event(sender: str, receiver: str, amount: int, memo: object = _MISSING) -> str:
    data = {"old_owner_id": sender, "new_owner_id": receiver, "amount": str(amount)}
    if memo is not _MISSING and memo is not None:
        data["memo"] = memo
    return "EVENT_JSON:" + json.dumps(
        {
            "standard": "nep141",
            "version": "1.0.0",
            "event": "ft_transfer",
            "data": [data],
        },
        separators=(",", ":"),
        ensure_ascii=False,
    )


def _ft_transfer(
    client: NearClient,
    receiver: str,
    amount: int,
    *,
    signer: str | None = None,
    memo: object = _MISSING,
    wire: bytes | None = None,
) -> None:
    sender = signer or client.account_id
    response = client.call_on(
        client.account_id,
        "ft_transfer",
        wire if wire is not None else _ft_args(receiver, amount, memo),
        signer=signer,
        deposit=1,
    )
    if NearClient.success_value_bytes(response) != b"":
        raise AssertionError("ft_transfer success did not return exact empty bytes")
    expected = _transfer_event(sender, receiver, amount, memo)
    logs = _receipt_logs(response)
    if logs != [expected]:
        raise AssertionError(f"ft_transfer exact event mismatch: {logs!r} != {[expected]!r}")


def _ft_transfer_fails(
    client: NearClient,
    receiver: str,
    amount: int,
    scene: str,
    *,
    signer: str | None = None,
    deposit: int = 1,
    memo: object = _MISSING,
    wire: bytes | None = None,
) -> None:
    before = client.view_state_values()
    response = client.call_on(
        client.account_id,
        "ft_transfer",
        wire if wire is not None else _ft_args(receiver, amount, memo),
        signer=signer,
        deposit=deposit,
        expect_success=False,
    )
    if _receipt_logs(response):
        raise AssertionError(f"{scene}: rejected transfer emitted a log")
    if client.view_state_values() != before:
        raise AssertionError(f"{scene}: rejected transfer changed durable state")


def _ft_transfer_call_args(
    receiver: str, amount: int, msg: str, memo: object = _MISSING
) -> bytes:
    fields: dict[str, object] = {
        "receiver_id": receiver,
        "amount": str(amount),
        "msg": msg,
    }
    if memo is not _MISSING:
        fields["memo"] = memo
    return json.dumps(fields, separators=(",", ":"), ensure_ascii=False).encode()


def _ft_transfer_call(
    client: NearClient,
    receiver: str,
    amount: int,
    msg: str,
    expected_used: int,
    refund: int,
    *,
    signer: str | None = None,
    memo: object = _MISSING,
    child_failure: bool = False,
) -> dict:
    sender = signer or client.account_id
    response = client.call_on(
        client.account_id,
        "ft_transfer_call",
        _ft_transfer_call_args(receiver, amount, msg, memo),
        signer=signer,
        deposit=1,
        gas=200_000_000_000_000,
        # A failed child is expected to be recovered by the dependent resolver. near_rpc's
        # conservative checker still reports the intermediate failed receipt.
        expect_success=not child_failure,
    )
    raw = NearClient.success_value_bytes(response)
    wanted = f'"{expected_used}"'.encode()
    if raw != wanted:
        raise AssertionError(f"ft_transfer_call output {raw!r} != {wanted!r}")
    expected_logs = [_transfer_event(sender, receiver, amount, memo)]
    if refund:
        expected_logs.append(_resolver_event("ft_transfer", receiver, refund, sender=sender))
    logs = _receipt_logs(response)
    if logs != expected_logs:
        raise AssertionError(
            f"ft_transfer_call exact event sequence {logs!r} != {expected_logs!r}"
        )
    return response


def _ft_transfer_call_fails(
    client: NearClient,
    receiver: str,
    amount: int,
    scene: str,
    *,
    signer: str | None = None,
    deposit: int = 1,
    msg: str = "",
) -> None:
    before = client.view_state_values()
    response = client.call_on(
        client.account_id,
        "ft_transfer_call",
        _ft_transfer_call_args(receiver, amount, msg),
        signer=signer,
        deposit=deposit,
        gas=200_000_000_000_000,
        expect_success=False,
    )
    if _receipt_logs(response):
        raise AssertionError(f"{scene}: rejected transfer-call emitted an event")
    if client.view_state_values() != before:
        raise AssertionError(f"{scene}: rejected transfer-call changed durable state")


def _resolver_event(kind: str, owner: str, amount: int, *, sender: str | None = None) -> str:
    if kind == "ft_transfer":
        data = {
            "old_owner_id": owner,
            "new_owner_id": sender,
            "amount": str(amount),
            "memo": "refund",
        }
    else:
        data = {"owner_id": owner, "amount": str(amount), "memo": "refund"}
    return "EVENT_JSON:" + json.dumps(
        {"standard": "nep141", "version": "1.0.0", "event": kind, "data": [data]},
        separators=(",", ":"),
    )


def _resolve(
    client: NearClient,
    method: str,
    expected: int | None,
    *,
    event: str | None = None,
    expect_success: bool = True,
    child_failure: bool = False,
    wire: bytes = b"",
) -> dict:
    before = client.view_state_values()
    response = client.call_on(
        client.account_id,
        method,
        wire,
        gas=100_000_000_000_000,
        # near_rpc's conservative receipt checker treats a failed child as transaction failure
        # even when the dependent resolver succeeds. Opt into that expected intermediate failure
        # while still checking the callback's final SuccessValue below.
        expect_success=expect_success and not child_failure,
    )
    logs = _receipt_logs(response)
    if expect_success:
        raw = NearClient.success_value_bytes(response)
        wanted = f'"{expected}"'.encode()
        if raw != wanted:
            raise AssertionError(f"{method}: resolver output {raw!r} != {wanted!r}")
        wanted_logs = [] if event is None else [event]
        if logs != wanted_logs:
            raise AssertionError(f"{method}: resolver logs {logs!r} != {wanted_logs!r}")
    else:
        if logs:
            raise AssertionError(f"{method}: failed resolver emitted logs {logs!r}")
        if client.view_state_values() != before:
            raise AssertionError(f"{method}: failed callback changed durable state")
    return response


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    client.deploy(wasm)
    client.call("initialize", b"")
    self_id = client.account_id
    self_key = _key(self_id)
    resolver_contract = f"resolver.{self_id}"
    client.create_subaccount_with_key(resolver_contract, 10**25)
    client.deploy_to(resolver_contract, wasm)
    client.call_on(resolver_contract, "initialize", b"", signer=resolver_contract)
    fixture_dir = Path(_require("PF_NEAR_FIXTURE_DIR"))
    for outcome in ("partial", "full", "malformed", "failed"):
        account = f"{outcome}.{self_id}"
        client.create_subaccount_with_key(account, 10**25)
        client.deploy_to(account, fixture_dir / f"ft-on-transfer-{outcome}.wasm")
    child_result = f"json-result.{self_id}"
    client.create_subaccount_with_key(child_result, 10**25)
    client.deploy_to(child_result, fixture_dir / "ft-receiver-result.wasm")

    if _view(client, "balanceSelfHas") != 0 or _balance(client.view_state_values(), self_id) is not None:
        raise AssertionError("missing balance must remain distinct from present zero")
    if _json_balance(client, b"missing.test.near") != 0:
        raise AssertionError("ft_balance_of missing account did not return quoted zero")
    if _json_supply(client) != 0:
        raise AssertionError("ft_total_supply initial value was not quoted zero")
    metadata_before = client.view_state_values()
    expected_metadata = _metadata_wire()
    for wire in (b"", b"{}", b'{"unused":0}', b"not-json", b"{}"):
        if client.view("ft_metadata", wire) != expected_metadata:
            raise AssertionError("integrated ft_metadata request-ignore or exact bytes mismatch")
    if client.view_state_values() != metadata_before:
        raise AssertionError("integrated ft_metadata changed ledger state")
    if client.view("storage_balance_bounds", b"") != b'{"min":"66","max":"128"}':
        raise AssertionError("integrated storage_balance_bounds geometry mismatch")
    for wire in (b"{}", b"not-json", b"\xff" * 4096):
        if client.view("storage_balance_bounds", wire) != b'{"min":"66","max":"128"}':
            raise AssertionError("integrated storage bounds did not ignore request bytes")
    if _storage_balance(client, "aa") != b"null":
        raise AssertionError("integrated storage_balance_of missing account was not null")
    for wire in (b"{}", b"not-json", b"\xff" * 4096):
        if _json_supply(client, wire) != 0:
            raise AssertionError("ft_total_supply no-args wrapper changed result for ignored bytes")
    try:
        client.view("balanceSelfHas", b"{}")
    except NearRpcError:
        pass
    else:
        raise AssertionError("unannotated zero-argument view stopped requiring empty input")
    _fail_unchanged(client, "burnSelfOne", "missing-balance underflow")
    before = client.view_state_values()
    _call(client, "mintSelfZero")
    after = client.view_state_values()
    if _view(client, "balanceSelfHas") != 0 or _supply(client) != 0 or self_key in after:
        raise AssertionError(
            f"zero mint must validate missing-as-zero without a ledger mutation: "
            f"before={before!r}, after={after!r}"
        )
    before_underfunded = client.view_state_values()
    client.call_on(
        client.account_id, "storage_deposit", b"{}", signer=client.account_id,
        deposit=1, expect_success=False,
    )
    if client.view_state_values() != before_underfunded or self_key in client.view_state_values():
        raise AssertionError("underfunded storage_deposit did not roll back speculative BAL2 write")
    self_cost = len(client.account_id.encode()) + 64
    deposit = 10_000
    registered = client.call_on(
        client.account_id, "storage_deposit", b"{}", signer=client.account_id,
        deposit=deposit,
    )
    expected_registration = f'{{"total":"{self_cost}","available":"0"}}'.encode()
    if NearClient.success_value_bytes(registered) != expected_registration:
        raise AssertionError("integrated storage_deposit new-account output mismatch")
    _assert_transfer_receipt(client, registered, client.account_id, deposit - self_cost)
    if _storage_balance(client, client.account_id) != expected_registration:
        raise AssertionError("integrated storage_deposit did not create BAL2 registration")
    duplicate = client.call_on(
        client.account_id, "storage_deposit", b'{"registration_only":true}',
        signer=client.account_id, deposit=7,
    )
    _assert_transfer_receipt(client, duplicate, client.account_id, 7)
    before_bad_deposit = client.view_state_values()
    client.call_on(
        client.account_id, "storage_deposit", b'{"unknown":null}',
        signer=client.account_id, deposit=100, expect_success=False,
    )
    if client.view_state_values() != before_bad_deposit:
        raise AssertionError("malformed integrated storage_deposit changed ledger state")
    _call(client, "fixtureResetSelf")
    if _storage_balance(client, client.account_id) != b"null":
        raise AssertionError("storage_deposit registration did not share BAL2 lifecycle")
    explicit = client.call_on(
        client.account_id, "storage_deposit",
        b'{"account_id":"aa","registration_only":true}',
        signer=client.account_id, deposit=100,
    )
    if NearClient.success_value_bytes(explicit) != b'{"total":"66","available":"0"}':
        raise AssertionError("explicit integrated storage_deposit result mismatch")
    _assert_transfer_receipt(client, explicit, client.account_id, 34)
    if _storage_balance(client, "aa") != b'{"total":"66","available":"0"}':
        raise AssertionError("explicit storage_deposit did not use canonical BAL2 account key")
    _call(client, "fixtureRemoveViewAccounts")
    print("near-ledger: metadata, missing/zero policy, and zero no-ledger-mutation ok")

    _call(client, "fixturePutSelfZeroNoSupply")
    present_zero = client.view_state_values()
    expected_self_cost = len(client.account_id.encode()) + 64
    expected_self_balance = (
        f'{{"total":"{expected_self_cost}","available":"0"}}'.encode()
    )
    if _storage_balance(client, client.account_id) != expected_self_balance:
        raise AssertionError("integrated storage_balance_of present-zero cost mismatch")
    if self_key not in present_zero or len(present_zero[self_key]) != 16:
        raise AssertionError("fixture present-zero balance was not stored exactly")
    if _view(client, "balanceSelfHas") != 1 or _json_balance(client, self_id.encode()) != 0:
        raise AssertionError("present zero was not distinguishable from missing in storage")
    _call(client, "fixtureResetSelf")

    short_id = "aa"
    max_id = "abcdefgh01234567ijklmnop89abcdefqrstuvwx76543210yzabcdef01234567"
    _call(client, "fixturePutShortNoSupply")
    if _json_balance(client, short_id.encode()) != (1 << 64) + 3:
        raise AssertionError("short AccountId lookup included inactive carrier padding")
    if _storage_balance(client, short_id) != b'{"total":"66","available":"0"}':
        raise AssertionError("short registration geometry did not use active AccountId bytes")
    _call(client, "fixturePutMaxAccountNoSupply")
    if _json_balance(client, max_id.encode()) != MAX_U128:
        raise AssertionError("maximum asymmetric AccountId/u128 lookup mismatch")
    if _storage_balance(client, max_id) != b'{"total":"128","available":"0"}':
        raise AssertionError("maximum registration geometry mismatch")
    if _json_balance(client, max_id.replace("a", "\\u0061", 1).encode()) != MAX_U128:
        raise AssertionError("escaped maximum AccountId lookup mismatch")
    _call(client, "fixtureRemoveViewAccounts")
    state = client.view_state_values()
    if _key(short_id) in state or _key(max_id) in state:
        raise AssertionError("view fixture accounts were not reclaimed")
    print("near-ledger: present zero plus short/max canonical AccountId views ok")

    _call(client, "seedSelfMalformed8")
    malformed8 = client.view_state_values()
    if len(malformed8[self_key]) != 8:
        raise AssertionError("malformed-short seed geometry mismatch")
    _json_balance_fails(client, self_id.encode(), "malformed-short balance")
    try:
        _storage_balance(client, self_id)
    except NearRpcError:
        pass
    else:
        raise AssertionError("malformed-short storage_balance_of did not fail closed")
    _fail_unchanged(client, "mintSelfOne", "malformed-short balance")
    if client.view_state_values() != malformed8:
        raise AssertionError("malformed-short rejection lost exact snapshot")
    _call(client, "fixtureResetSelf")

    _call(client, "seedSelfMalformed20")
    malformed20 = client.view_state_values()
    if len(malformed20[self_key]) != 20:
        raise AssertionError("malformed-long seed geometry mismatch")
    _json_balance_fails(client, self_id.encode(), "malformed-long balance")
    try:
        _storage_balance(client, self_id)
    except NearRpcError:
        pass
    else:
        raise AssertionError("malformed-long storage_balance_of did not fail closed")
    _fail_unchanged(client, "burnSelfZero", "malformed-long zero burn")
    if client.view_state_values() != malformed20:
        raise AssertionError("malformed-long rejection exposed partial/stale data")
    _call(client, "fixtureResetSelf")
    if _json_balance(client, self_id.encode()) != 0:
        raise AssertionError("normal read after malformed views observed stale register data")
    print("near-ledger: present malformed 8/20-byte balances fail closed before writes ok")

    _call(client, "fixturePutSelfMaxNoSupply")
    _fail_unchanged(client, "mintSelfOne", "balance overflow")
    _call(client, "fixtureResetSelf")
    _call(client, "fixtureSetSupplyMax")
    _fail_unchanged(client, "mintSelfOne", "supply overflow after balance precheck")
    _call(client, "fixtureResetSelf")
    _call(client, "fixturePutSelfOneNoSupply")
    _fail_unchanged(client, "burnSelfOne", "supply underflow after balance precheck")
    _call(client, "fixtureResetSelf")
    print("near-ledger: balance/supply overflow and supply underflow are write-free ok")

    _call(client, "mintSelfTwo64")
    if _json_supply(client) != 1 << 64:
        raise AssertionError("ft_total_supply high-limb-only value mismatch")
    _call(client, "mintSelfOne")
    mixed = (1 << 64) + 1
    state = client.view_state_values()
    if _balance(state, self_id) != mixed or _supply(client) != mixed:
        raise AssertionError("mixed low/high mint did not preserve both limbs")
    if _json_supply(client) != mixed:
        raise AssertionError("ft_total_supply mixed limbs mismatch")
    if _json_balance(client, self_id.encode()) != mixed or \
        _json_balance(client, self_id.replace(".", "\\u002e").encode()) != mixed:
        raise AssertionError("ft_balance_of raw/escaped self query lost mixed limbs")
    _call(client, "burnSelfZero")
    after_zero = client.view_state_values()
    if _balance(after_zero, self_id) != mixed or _supply(client) != mixed:
        raise AssertionError("zero burn must validate without a ledger mutation")
    _call(client, "transferCallerToSelfOne")
    after_alias = client.view_state_values()
    if _balance(after_alias, self_id) != mixed or _supply(client) != mixed:
        raise AssertionError("from==to transfer must check sufficiency without a ledger mutation")
    print("near-ledger: mixed limbs, zero burn, and alias-safe self transfer ok")

    caller = f"ledger-caller.{self_id}"
    client.create_subaccount_with_key(caller, 10**25)
    caller_key = _key(caller)

    unregistered = f"ledger-unregistered.{self_id}"
    client.create_subaccount_with_key(unregistered, 10**24)
    _call(client, "fixturePutSelfZeroNoSupply")
    _ft_transfer_fails(client, self_id, 1, "unregistered source", signer=unregistered)
    _call(client, "mintCallerOne", signer=caller)
    _ft_transfer_fails(client, "absent-ledger.test.near", 1, "unregistered destination", signer=caller)
    _ft_transfer_fails(client, caller, 1, "sender equals receiver", signer=caller)
    _ft_transfer_fails(client, self_id, 0, "zero amount", signer=caller)
    _ft_transfer_fails(client, self_id, 1, "zero attached deposit", signer=caller, deposit=0)
    _ft_transfer_fails(client, self_id, 1, "two yocto attached deposit", signer=caller, deposit=2)
    _ft_transfer_fails(client, self_id, MAX_U128, "insufficient balance", signer=caller)
    _ft_transfer_fails(
        client,
        self_id,
        1,
        "duplicate input field",
        signer=caller,
        wire=(b'{"receiver_id":"' + self_id.encode() +
              b'","amount":"1","amount":"1"}'),
    )
    _call(client, "seedSelfMalformed8")
    _ft_transfer_fails(client, self_id, 1, "malformed destination", signer=caller)
    _call(client, "fixtureResetSelf")
    _call(client, "fixtureResetCaller", signer=caller)
    _call(client, "seedSelfMalformed20")
    _call(client, "mintCallerOne", signer=caller)
    _ft_transfer_fails(client, caller, 1, "malformed source")
    _call(client, "fixtureResetSelf")
    _call(client, "fixtureResetCaller", signer=caller)
    print("near-ledger: ft_transfer guards, registration, malformed values, and rollback ok")

    _call(client, "fixturePutSelfMaxNoSupply")
    _call(client, "mintCallerOne", signer=caller)
    _ft_transfer_fails(client, self_id, 1, "ft_transfer destination overflow", signer=caller)
    _call(client, "fixtureResetSelf")
    _call(client, "fixtureResetCaller", signer=caller)

    _call(client, "fixturePutSelfZeroNoSupply")
    _call(client, "mintCallerTwo64", signer=caller)
    high_supply = _supply(client)
    _ft_transfer(client, self_id, 1 << 64, signer=caller)
    high_state = client.view_state_values()
    if _balance(high_state, caller) != 0 or caller_key not in high_state:
        raise AssertionError("ft_transfer did not preserve registered present-zero source")
    if _balance(high_state, self_id) != 1 << 64 or _supply(client) != high_supply:
        raise AssertionError("ft_transfer high-limb transfer changed supply or limb order")
    _call(client, "fixtureResetSelf")
    _call(client, "fixtureResetCaller", signer=caller)

    _call(client, "fixturePutSelfZeroNoSupply")
    for _ in range(5):
        _call(client, "mintCallerOne", signer=caller)
    transfer_supply = _supply(client)
    _ft_transfer(client, self_id, 1, signer=caller)
    _ft_transfer(client, self_id, 1, signer=caller, memo=None)
    _ft_transfer(client, self_id, 1, signer=caller, memo="")
    _ft_transfer(client, self_id, 1, signer=caller, memo='"\\\b\t\n')
    # Exercise any-order field dispatch plus decoded non-ASCII memo bytes.
    permuted = json.dumps(
        {"memo": "雪😀", "amount": "1", "receiver_id": self_id},
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode()
    _ft_transfer(client, self_id, 1, signer=caller, memo="雪😀", wire=permuted)
    transfer_state = client.view_state_values()
    if _balance(transfer_state, caller) != 0 or caller_key not in transfer_state:
        raise AssertionError("final ft_transfer did not retain zero balance registration")
    if _balance(transfer_state, self_id) != 5 or _supply(client) != transfer_supply:
        raise AssertionError("ft_transfer memo scenes violated balance/supply conservation")
    print("near-ledger: exact empty output, u128 transfer, optional memo events, and conservation ok")

    _call(client, "fixtureResetSelf")
    _call(client, "fixtureResetCaller", signer=caller)
    _call(client, "mintCallerTwo64", signer=caller)
    _call(client, "mintCallerOne", signer=caller)
    if _json_balance(client, caller.encode()) != (1 << 64) + 1:
        raise AssertionError("ft_balance_of caller query lost complete AccountId/u128")
    before_supply = _supply(client)
    _call(client, "transferCallerToSelfOne", signer=caller)
    if _supply(client) != before_supply:
        raise AssertionError("distinct transfer changed total supply")
    _call(client, "transferCallerToSelfTwo64", signer=caller)
    state = client.view_state_values()
    if caller_key in state:
        raise AssertionError("zero source balance was not reclaimed")
    self_balance = _balance(state, self_id)
    if self_balance != _supply(client) or self_balance != (1 << 64) + 1:
        raise AssertionError("distinct transfer violated conservation or limb ordering")
    _fail_unchanged(
        client, "transferCallerToSelfOne", "missing-source transfer", signer=caller
    )
    print("near-ledger: distinct transfer snapshots, reclamation, and conservation ok")

    _call(client, "fixtureResetSelf")
    _call(client, "mintSelfMax")
    if _balance(client.view_state_values(), self_id) != MAX_U128 or _supply(client) != MAX_U128:
        raise AssertionError("maximum u128 mint mismatch")
    if _json_balance(client, self_id.encode()) != MAX_U128:
        raise AssertionError("ft_balance_of maximum quoted u128 mismatch")
    if _json_supply(client) != MAX_U128:
        raise AssertionError("ft_total_supply maximum quoted u128 mismatch")
    _call(client, "burnSelfMax")
    if self_key in client.view_state_values() or _supply(client) != 0:
        raise AssertionError("maximum burn did not reclaim balance and zero supply")
    if _json_supply(client) != 0:
        raise AssertionError("ft_total_supply did not return quoted zero after maximum burn")
    print("near-ledger: maximum u128 mint/burn and zero reclamation ok")

    _call(client, "mintCallerOne", signer=caller)
    _call(client, "fixturePutSelfMaxNoSupply")
    _fail_unchanged(
        client, "transferCallerToSelfOne", "destination overflow", signer=caller
    )
    state = client.view_state_values()
    if _balance(state, caller) != 1 or _balance(state, self_id) != MAX_U128 or _supply(client) != 1:
        raise AssertionError("destination-overflow rejection changed a source/destination snapshot")
    print("near-ledger: destination overflow validates both snapshots before either write ok")

    # Exact public-shaped ft_transfer_call composes the bounded four-field parser, initial BAL2
    # transfer/event, dynamic weighted child call, private resolver, and returned callback Promise.
    _call(client, "fixtureTransferCall")
    _ft_transfer_call_fails(client, self_id, 1, "transfer-call sender equals receiver")
    _ft_transfer_call_fails(client, "partial.test.near", 0, "transfer-call zero amount")
    _ft_transfer_call_fails(
        client, "partial.test.near", 1, "transfer-call zero deposit", deposit=0
    )
    _ft_transfer_call_fails(
        client, "partial.test.near", 1, "transfer-call two-yocto deposit", deposit=2
    )
    _ft_transfer_call_fails(
        client, "absent-ledger.test.near", 1, "transfer-call unregistered destination"
    )
    _ft_transfer_call_fails(
        client, "partial.test.near", MAX_U128, "transfer-call insufficient source"
    )
    _ft_transfer_call_fails(
        client,
        "partial.test.near",
        1,
        "transfer-call unregistered source",
        signer=unregistered,
    )

    _call(client, "fixtureTransferCall")
    _call(client, "seedSelfMalformed8")
    _ft_transfer_call_fails(
        client, "partial.test.near", 1, "transfer-call malformed source"
    )
    _call(client, "fixtureTransferCall")
    _call(client, "mintCallerOne", signer=caller)
    _call(client, "seedSelfMalformed20")
    _ft_transfer_call_fails(
        client, self_id, 1, "transfer-call malformed destination", signer=caller
    )
    _call(client, "fixtureTransferCall")
    _call(client, "mintCallerOne", signer=caller)
    _call(client, "fixturePutSelfMaxNoSupply")
    _ft_transfer_call_fails(
        client, self_id, 1, "transfer-call destination overflow", signer=caller
    )
    print("near-ledger: ft_transfer_call guards/read checks fail before effects or Promise creation ok")

    transfer_call_supply = (1 << 64) + 1
    transfer_call_scenes = (
        ("partial.test.near", 10, 7, 3, transfer_call_supply - 7, 7,
         _MISSING, "雪😀\x00", False),
        ("partial.test.near", 1 << 64, (1 << 64) - 3, 3, 4, (1 << 64) - 3,
         _MISSING, "high-limb", False),
        ("full.test.near", 10, 0, 10, transfer_call_supply, 0,
         None, "m" * 64, False),
        ("malformed.test.near", 10, 0, 10, transfer_call_supply, 0,
         "", "bad-result", False),
        ("failed.test.near", 10, 0, 10, transfer_call_supply, 0,
         "雪\n", "failed", True),
    )
    for (
        receiver, amount, used, refund, sender_after, receiver_after, memo, msg, child_failed
    ) in transfer_call_scenes:
        _call(client, "fixtureTransferCall")
        _ft_transfer_call(
            client,
            receiver,
            amount,
            msg,
            used,
            refund,
            memo=memo,
            child_failure=child_failed,
        )
        state = client.view_state_values()
        if _balance(state, self_id) != sender_after or _balance(state, receiver) != receiver_after:
            raise AssertionError(f"{receiver}: transfer-call BAL2 reconciliation mismatch")
        if _key(receiver) not in state:
            raise AssertionError(f"{receiver}: transfer-call removed receiver registration")
        if _supply(client) != transfer_call_supply:
            raise AssertionError(f"{receiver}: transfer-call changed conserved supply")
    print("near-ledger: exact ft_transfer_call partial/full/malformed/failed returned chains ok")

    # Specialized ft_on_transfer → real private resolver chains. The fixture account IDs exactly
    # match the BAL2 seed keys and the transaction predecessor is the callback sender_id.
    chain_scenes = (
        ("fixtureChainPartialPresent", "chainPartial", "partial.test.near", 7, 5, 4, 9,
         _resolver_event("ft_transfer", "partial.test.near", 3, sender=self_id), False),
        ("fixtureChainFullMissing", "chainFull", "full.test.near", 10, None, 0, 0,
         _resolver_event("ft_burn", "full.test.near", 7), False),
        ("fixtureChainMalformedPresent", "chainMalformed", "malformed.test.near", 3, 9, 0, 9,
         _resolver_event("ft_transfer", "malformed.test.near", 7, sender=self_id), False),
        ("fixtureChainFailedPresent", "chainFailed", "failed.test.near", 3, 9, 0, 9,
         _resolver_event("ft_transfer", "failed.test.near", 7, sender=self_id), True),
    )
    for seed, method, receiver, used, sender_balance, receiver_balance, supply, event, child_failed in chain_scenes:
        _call(client, seed)
        response = _resolve(client, method, used, event=event, child_failure=child_failed,
                            wire=b'{"msg":"chain"}')
        if NearClient.success_value_bytes(response) != f'"{used}"'.encode():
            raise AssertionError(f"{method}: outer receipt did not forward exact quoted callback bytes")
        state = client.view_state_values()
        if _balance(state, self_id) != sender_balance or _balance(state, receiver) != receiver_balance:
            raise AssertionError(f"{method}: BAL2 reconciliation mismatch")
        if receiver_balance == 0 and _key(receiver) not in state:
            raise AssertionError(f"{method}: receiver present-zero registration was removed")
        if _supply(client) != supply:
            raise AssertionError(f"{method}: supply conservation/burn mismatch")
    print("near-ledger: specialized partial/full/malformed/failed chains reconcile real BAL2 state ok")

    # Genuine child → private callback chains exercise the strict result decoder and the same BAL2
    # map. Short aa/bb callback identities keep static fixture args within the Promise64 budget.
    sender_id, receiver_id = "aa", "bb"
    sender_key, receiver_key = _key(sender_id), _key(receiver_id)

    _call(client, "fixtureResetResolver")
    _call(client, "fixtureResolverPresent")
    _resolve(
        client,
        "resolveUnusedThree",
        7,
        event=_resolver_event("ft_transfer", receiver_id, 3, sender=sender_id),
    )
    state = client.view_state_values()
    if _balance(state, sender_id) != 5 or _balance(state, receiver_id) != 4 or _supply(client) != 9:
        raise AssertionError(
            "present-sender resolver violated refund conservation: "
            f"sender={_balance(state, sender_id)} receiver={_balance(state, receiver_id)} "
            f"supply={_supply(client)}"
        )

    _call(client, "fixtureResolverPresent")
    _resolve(
        client,
        "resolveUnusedTwenty",
        3,
        event=_resolver_event("ft_transfer", receiver_id, 7, sender=sender_id),
    )
    state = client.view_state_values()
    if _balance(state, sender_id) != 9 or _balance(state, receiver_id) != 0 or receiver_key not in state:
        raise AssertionError("resolver clamp did not preserve receiver present-zero registration")
    if _supply(client) != 9:
        raise AssertionError("present-sender clamp changed supply")

    for method in ("resolveMalformed", "resolveOversized"):
        _call(client, "fixtureResolverPresent")
        _resolve(
            client,
            method,
            3,
            event=_resolver_event("ft_transfer", receiver_id, 7, sender=sender_id),
        )
    _call(client, "fixtureResolverPresent")
    _resolve(
        client,
        "resolveFailed",
        3,
        event=_resolver_event("ft_transfer", receiver_id, 7, sender=sender_id),
        child_failure=True,
    )
    print("near-ledger: valid clamp and failed/malformed/oversized fallback refunds ok")

    _call(client, "fixtureResolverPresent")
    before = client.view_state_values()
    _resolve(client, "resolveUnusedZero", 10)
    if client.view_state_values() != before:
        raise AssertionError("zero unused amount performed a ledger write")

    _call(client, "fixtureResolverMissingReceiver")
    before = client.view_state_values()
    _resolve(client, "resolveUnusedThree", 10)
    if client.view_state_values() != before or receiver_key in before:
        raise AssertionError("missing receiver was created by zero-refund resolution")

    _call(client, "fixtureResolverReceiverZero")
    before = client.view_state_values()
    _resolve(client, "resolveUnusedThree", 10)
    if client.view_state_values() != before or _balance(before, receiver_id) != 0:
        raise AssertionError("present-zero receiver changed on zero refund")

    _call(client, "fixtureResolverMissingSender")
    _resolve(
        client,
        "resolveUnusedThree",
        10,
        event=_resolver_event("ft_burn", receiver_id, 3),
    )
    state = client.view_state_values()
    if sender_key in state or _balance(state, receiver_id) != 4 or _supply(client) != 4:
        raise AssertionError("deleted-sender burn did not preserve conservation")
    print("near-ledger: zero/missing receiver and deleted-sender burn return semantics ok")

    for seed, method in (
        ("fixtureResolverMalformedReceiver", "resolveUnusedThree"),
        ("fixtureResolverMalformedSender", "resolveUnusedThree"),
        ("fixtureResolverSenderMax", "resolveUnusedThree"),
        ("fixtureResolverSupplyUnderflow", "resolveUnusedThree"),
    ):
        _call(client, seed)
        _resolve(client, method, None, expect_success=False)

    _call(client, "fixtureResolverPresent")
    _resolve(client, "resolveCountZero", None, expect_success=False)
    _call(client, "fixtureResolverPresent")
    _resolve(client, "resolvePaidCallback", None, expect_success=False)
    before = client.view_state_values()
    client.call_on(
        client.account_id,
        "ft_resolve_transfer",
        b'{"sender_id":"aa","receiver_id":"bb","amount":"10"}',
        expect_success=False,
    )
    if client.view_state_values() != before:
        raise AssertionError("direct private resolver call changed state")
    print("near-ledger: private/nonpayable/count/malformed/overflow failures roll back without events ok")

    # Redeploy one already registered receiver only after every fixed-WAT scene above. One exact
    # ft_on_transfer method now selects immediate U128 or returned Promise at runtime; the token's
    # real ft_transfer_call/resolver chain observes both terminals and reconciles the same BAL2 map.
    dual_receiver = "partial.test.near"
    client.deploy_to(dual_receiver, Path(_require("PF_NEAR_RECEIVER_DUAL_WASM")))
    client.call_on(dual_receiver, "initialize", b"", signer=dual_receiver)
    dual_scenes = (
        ("", 0, 0, 10, transfer_call_supply, 0, False),
        ("a", 1, 10, 0, transfer_call_supply - 10, 10, False),
        ("ab", 2, 7, 3, transfer_call_supply - 7, 7, False),
        ("雪", 3, 7, 3, transfer_call_supply - 7, 7, False),
        ("abcd", 4, 0, 10, transfer_call_supply, 0, True),
        ("abcde", 5, 0, 10, transfer_call_supply, 0, False),
    )
    for call_index, (
        msg, decoded_length, used, refund, sender_after, receiver_after, child_failed
    ) in enumerate(dual_scenes, start=1):
        _call(client, "fixtureTransferCall")
        _ft_transfer_call(
            client,
            dual_receiver,
            10,
            msg,
            used,
            refund,
            child_failure=child_failed,
        )
        state = client.view_state_values()
        if _balance(state, self_id) != sender_after or _balance(state, dual_receiver) != receiver_after:
            raise AssertionError(f"dual receiver msg byte length {decoded_length}: BAL2 reconciliation mismatch")
        if _key(dual_receiver) not in state or _supply(client) != transfer_call_supply:
            raise AssertionError(f"dual receiver msg byte length {decoded_length}: registration/supply changed")
        if client.view_u64_on(dual_receiver, "get") != call_index or \
                client.view_u64_on(dual_receiver, "lastMsgLength") != decoded_length:
            raise AssertionError(
                f"dual receiver msg byte length {decoded_length}: state did not persist before terminal"
            )

    calls_before = client.view_u64_on(dual_receiver, "get")
    valid_wire = json.dumps(
        {"sender_id": self_id, "amount": "10", "msg": "rollback"},
        separators=(",", ":"),
    ).encode()
    client.call_on(dual_receiver, "ft_on_transfer", valid_wire, deposit=1, expect_success=False)
    client.call_on(dual_receiver, "ft_on_transfer", valid_wire + b"0", expect_success=False)
    if client.view_u64_on(dual_receiver, "get") != calls_before:
        raise AssertionError("dual receiver nonpayable/parse failure did not roll state back")
    client.call_on(dual_receiver, "fixtureSetCallsMax", b"")
    _call(client, "fixtureTransferCall")
    _ft_transfer_call(client, dual_receiver, 10, "a", 0, 10, child_failure=True)
    state = client.view_state_values()
    if _balance(state, self_id) != transfer_call_supply or _balance(state, dual_receiver) != 0 or \
            _supply(client) != transfer_call_supply:
        raise AssertionError("dual receiver source error did not trigger full resolver refund")
    if client.view_u64_on(dual_receiver, "get") != (1 << 64) - 1 or \
            client.view_u64_on(dual_receiver, "lastMsgLength") != 63:
        raise AssertionError("dual receiver source error changed state before failed receipt")
    print("near-ledger: runtime immediate/Promise receiver branches reconcile end-to-end and roll back ok")
    print("suite NearFungibleLedger: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-ledger: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
