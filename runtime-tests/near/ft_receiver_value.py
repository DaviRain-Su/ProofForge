#!/usr/bin/env python3
"""Immediate-value standards-shaped FT receiver boundary against near-sandbox."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError

OBSERVER = "observer.test.near"


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-ft-receiver-value: missing env {name}")
    return value


def _wire(sender: str, amount: int, msg: str) -> bytes:
    return json.dumps({"sender_id": sender, "amount": str(amount), "msg": msg},
                      ensure_ascii=False, separators=(",", ":")).encode()


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    receiver_wasm = Path(_require("PF_NEAR_RECEIVER_WASM"))
    promise_wasm = Path(_require("PF_NEAR_PROMISE_WASM"))

    print("=== suite: NearFtReceiverValue (immediate full-unused U128) ===")
    client.create_subaccount_with_key(OBSERVER, 10**27)
    client.deploy_to(OBSERVER, receiver_wasm)
    client.call_on(OBSERVER, "initialize", b"", signer=OBSERVER)

    amount = (1 << 127) + (1 << 64) + 7
    wire = _wire("sender.test.near", amount, "nul:\0 emoji:😀")
    direct = client.call_on(OBSERVER, "ft_on_transfer", wire)
    if NearClient.success_value_bytes(direct) != f'"{amount}"'.encode():
        raise AssertionError("immediate receiver did not return exact quoted full-u128 amount")
    if client.view_u64_on(OBSERVER, "get") != 1:
        raise AssertionError("successful immediate receiver did not persist state before output")

    client.call_on(OBSERVER, "ft_on_transfer", wire, deposit=1, expect_success=False)
    if client.view_u64_on(OBSERVER, "get") != 1:
        raise AssertionError("nonpayable receiver failure changed state")
    client.call_on(OBSERVER, "ft_on_transfer", wire + b"0", expect_success=False)
    if client.view_u64_on(OBSERVER, "get") != 1:
        raise AssertionError("receiver parse failure changed state")

    # A genuine weighted child call observes the receiver's quoted U128 as the outer result.
    client.deploy(promise_wasm)
    client.call("initialize", NearClient.encode_u64_le(0))
    client.call("setFtAmountLo", NearClient.encode_u64_le(amount & ((1 << 64) - 1)))
    client.call("setFtAmountHi", NearClient.encode_u64_le(amount >> 64))
    child = client.call("inspectFtOnTransfer", b'{"msg":"child"}')
    if NearClient.success_value_bytes(child) != f'"{amount}"'.encode():
        raise AssertionError("returned weighted child did not forward receiver quoted U128")
    if client.view_u64_on(OBSERVER, "get") != 2:
        raise AssertionError("weighted child did not execute the receiver exactly once")

    print("near-ft-receiver-value: output bytes, deposit guard, rollback, and real child result ok")
    print("suite NearFtReceiverValue: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-ft-receiver-value: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
