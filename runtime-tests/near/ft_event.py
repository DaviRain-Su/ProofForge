#!/usr/bin/env python3
"""Exact NEP-141 mint/transfer/burn events against local near-sandbox."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-ft-event: missing env {name}")
    return value


def _receipt_logs(response: dict) -> list[str]:
    return [
        log
        for receipt in response.get("receipts_outcome", ())
        for log in receipt.get("outcome", {}).get("logs", ())
    ]


def _expect_event(
    client: NearClient,
    method: str,
    event: str,
    data: dict[str, str],
    *,
    signer: str | None = None,
    memo: str | None = None,
) -> None:
    args = b"" if memo is None else NearClient.borsh_string(memo)
    response = client.call_on(client.account_id, method, args, signer=signer)
    if memo is not None:
        data = {**data, "memo": memo}
    expected = "EVENT_JSON:" + json.dumps(
        {
            "standard": "nep141",
            "version": "1.0.0",
            "event": event,
            "data": [data],
        },
        separators=(",", ":"),
        ensure_ascii=False,
    )
    logs = _receipt_logs(response)
    if logs != [expected]:
        raise AssertionError(f"{method}: expected {[expected]!r}, got {logs!r}")
    if memo is None and '"memo"' in logs[0]:
        raise AssertionError(f"{method}: memo must be omitted")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearFungibleTokenEvent (exact mint/transfer/burn events) ===")
    client.deploy(wasm)
    client.call("initialize")

    cases = (
        ("mintZero", 0),
        ("mintTwo64", 1 << 64),
        ("mintTwo64PlusOne", (1 << 64) + 1),
        ("mintMax", (1 << 128) - 1),
    )
    for method, amount in cases:
        _expect_event(
            client,
            method,
            "ft_mint",
            {"owner_id": client.account_id, "amount": str(amount)},
        )

    transfer_caller = "transfer-caller.test.near"
    client.create_subaccount_with_key(transfer_caller, 10**25)
    _expect_event(
        client,
        "transferMax",
        "ft_transfer",
        {
            "old_owner_id": transfer_caller,
            "new_owner_id": client.account_id,
            "amount": str((1 << 128) - 1),
        },
        signer=transfer_caller,
    )
    _expect_event(
        client,
        "burnTwo64",
        "ft_burn",
        {"owner_id": client.account_id, "amount": str(1 << 64)},
    )
    _expect_event(
        client,
        "mintMemo",
        "ft_mint",
        {"owner_id": client.account_id, "amount": "0"},
        memo="",
    )
    _expect_event(
        client,
        "transferMemo",
        "ft_transfer",
        {
            "old_owner_id": transfer_caller,
            "new_owner_id": client.account_id,
            "amount": str((1 << 64) + 1),
        },
        signer=transfer_caller,
        memo='"\\\b\t\n\f\r\x01',
    )
    _expect_event(
        client,
        "burnMemo",
        "ft_burn",
        {"owner_id": client.account_id, "amount": str((1 << 128) - 1)},
        memo="雪😀",
    )
    boundary_memo = "x" * 16
    _expect_event(
        client,
        "mintMemo",
        "ft_mint",
        {"owner_id": client.account_id, "amount": "0"},
        memo=boundary_memo,
    )
    expected_calls = len(cases) + 6
    if client.view_u64("get") != expected_calls:
        raise AssertionError("all event calls must commit exactly once")
    print("near-ft-event: exact fields, u128 decimal, bounded memo escaping, one log ok")
    print("suite NearFungibleTokenEvent: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-ft-event: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
