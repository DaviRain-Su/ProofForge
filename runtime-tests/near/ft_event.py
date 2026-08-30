#!/usr/bin/env python3
"""Exact no-memo NEP-141 ft_mint events against local near-sandbox."""

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


def _expect_mint(client: NearClient, method: str, amount: int) -> None:
    response = client.call(method)
    expected = "EVENT_JSON:" + json.dumps(
        {
            "standard": "nep141",
            "version": "1.0.0",
            "event": "ft_mint",
            "data": [{"owner_id": client.account_id, "amount": str(amount)}],
        },
        separators=(",", ":"),
    )
    logs = _receipt_logs(response)
    if logs != [expected]:
        raise AssertionError(f"{method}: expected {[expected]!r}, got {logs!r}")
    if '"memo"' in logs[0]:
        raise AssertionError(f"{method}: memo must be omitted")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearFungibleTokenEvent (exact ft_mint event) ===")
    client.deploy(wasm)
    client.call("initialize")

    cases = (
        ("mintZero", 0),
        ("mintTwo64", 1 << 64),
        ("mintTwo64PlusOne", (1 << 64) + 1),
        ("mintMax", (1 << 128) - 1),
    )
    for method, amount in cases:
        _expect_mint(client, method, amount)
    if client.view_u64("get") != len(cases):
        raise AssertionError("all four event methods must commit exactly once")
    print("near-ft-event: exact owner, 0/2^64/2^64+1/max-u128 decimal, no memo, one log ok")
    print("suite NearFungibleTokenEvent: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-ft-event: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
