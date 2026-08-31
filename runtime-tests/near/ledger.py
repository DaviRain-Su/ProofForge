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


def _json_supply_fails(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("ft_total_supply", wire)
    except NearRpcError:
        return
    raise AssertionError(f"{scene}: nonempty no-argument input was accepted")


def _receipt_logs(response: dict) -> list[str]:
    return [
        log
        for receipt in response.get("receipts_outcome", ())
        for log in receipt.get("outcome", {}).get("logs", ())
    ]


def _ft_args(receiver: str, amount: int, memo: object = _MISSING) -> bytes:
    fields: dict[str, object] = {"receiver_id": receiver, "amount": str(amount)}
    if memo is not _MISSING:
        fields["memo"] = memo
    return json.dumps(fields, separators=(",", ":"), ensure_ascii=False).encode()


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
    data = {"old_owner_id": sender, "new_owner_id": receiver, "amount": str(amount)}
    if memo is not _MISSING and memo is not None:
        data["memo"] = memo
    expected = "EVENT_JSON:" + json.dumps(
        {
            "standard": "nep141",
            "version": "1.0.0",
            "event": "ft_transfer",
            "data": [data],
        },
        separators=(",", ":"),
        ensure_ascii=False,
    )
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


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    wasm = Path(_require("PF_NEAR_WASM"))
    client.deploy(wasm)
    client.call("initialize", b"")
    self_id = client.account_id
    self_key = _key(self_id)

    if _view(client, "balanceSelfHas") != 0 or _balance(client.view_state_values(), self_id) is not None:
        raise AssertionError("missing balance must remain distinct from present zero")
    if _json_balance(client, b"missing.test.near") != 0:
        raise AssertionError("ft_balance_of missing account did not return quoted zero")
    if _json_supply(client) != 0:
        raise AssertionError("ft_total_supply initial value was not quoted zero")
    _json_supply_fails(client, b"{}", "empty JSON object")
    _json_supply_fails(client, b"not-json", "malformed nonempty bytes")
    _fail_unchanged(client, "burnSelfOne", "missing-balance underflow")
    before = client.view_state_values()
    _call(client, "mintSelfZero")
    after = client.view_state_values()
    if _view(client, "balanceSelfHas") != 0 or _supply(client) != 0 or self_key in after:
        raise AssertionError(
            f"zero mint must validate missing-as-zero without a ledger mutation: "
            f"before={before!r}, after={after!r}"
        )
    print("near-ledger: missing/zero policy and zero no-ledger-mutation ok")

    _call(client, "fixturePutSelfZeroNoSupply")
    present_zero = client.view_state_values()
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
    _call(client, "fixturePutMaxAccountNoSupply")
    if _json_balance(client, max_id.encode()) != MAX_U128:
        raise AssertionError("maximum asymmetric AccountId/u128 lookup mismatch")
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
    _fail_unchanged(client, "mintSelfOne", "malformed-short balance")
    if client.view_state_values() != malformed8:
        raise AssertionError("malformed-short rejection lost exact snapshot")
    _call(client, "fixtureResetSelf")

    _call(client, "seedSelfMalformed20")
    malformed20 = client.view_state_values()
    if len(malformed20[self_key]) != 20:
        raise AssertionError("malformed-long seed geometry mismatch")
    _json_balance_fails(client, self_id.encode(), "malformed-long balance")
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
    print("suite NearFungibleLedger: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-ledger: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
