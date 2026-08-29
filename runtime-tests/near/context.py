#!/usr/bin/env python3
"""NearCtx sandbox scenes for Runtime host reads (engineering only).

Scenes:
  initialize(0) → get()==0
  full current AccountId is length + zero-padded 64-byte words
  account_balance and attached_deposit preserve both u128 words
  explicit legacy deposit projection traps when the high word is nonzero
  direct call passes full predecessor == current-account self check
  height() equals status.sync_info.latest_block_height
  stamp() stores that height; get() matches SuccessValue
  seconds() is a view (unix seconds from block_timestamp)

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping context.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-context: missing env {name}")
    return v


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearCtx (account / u128 / height / time) ===")
    client.deploy(wasm)

    client.call("initialize", NearClient.encode_u64_le(0))
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize(0): get() expected 0, got {got}")
    print("nearctx: initialize(0) → get()==0 ok")

    self_id = client.view_u64("selfId")
    expected = int.from_bytes(b"test.nea", "little")
    if self_id != expected:
        raise AssertionError(
            f"selfId() expected first 8 UTF-8 bytes of test.near "
            f"({expected:#x}), got {self_id:#x}"
        )
    self_len = client.view_u64("selfIdLength")
    if self_len != len(b"test.near"):
        raise AssertionError(f"selfIdLength() expected 9, got {self_len}")
    self_w1 = client.view_u64("selfIdWord1")
    if self_w1 != ord("r"):
        raise AssertionError(f"selfIdWord1() expected zero-padded 'r', got {self_w1:#x}")
    print("nearctx: full self AccountId == len(9) + test.nea/r words ok")

    account_balance = client.view_account_balance(client.account_id)
    balance_low = client.view_u64("selfBal")
    balance_high = client.view_u64("selfBalHigh")
    if balance_low != account_balance & ((1 << 64) - 1):
        raise AssertionError(
            f"selfBal() expected account balance low word "
            f"{account_balance & ((1 << 64) - 1)}, got {balance_low}"
        )
    if balance_high != account_balance >> 64:
        raise AssertionError(
            f"selfBalHigh() expected account balance high word "
            f"{account_balance >> 64}, got {balance_high}"
        )
    print(f"nearctx: account_balance u128 == ({balance_high:#x}, {balance_low:#x}) ok")

    wide_deposit = (1 << 64) + 7
    low_res = client.call("takeDeposit", b"", deposit=wide_deposit)
    low_value = NearClient.success_value_bytes(low_res)
    if low_value is None or len(low_value) < 8:
        raise AssertionError(f"takeDeposit SuccessValue expected ≥8 bytes, got {low_value!r}")
    if NearClient.decode_u64_le(low_value, 0) != 7:
        raise AssertionError("takeDeposit must preserve the low word of a >u64 deposit")
    high_res = client.call("takeDepositHigh", b"", deposit=wide_deposit)
    high_value = NearClient.success_value_bytes(high_res)
    if high_value is None or len(high_value) < 8:
        raise AssertionError(
            f"takeDepositHigh SuccessValue expected ≥8 bytes, got {high_value!r}"
        )
    if NearClient.decode_u64_le(high_value, 0) != 1:
        raise AssertionError("takeDepositHigh must preserve the high word of a >u64 deposit")
    client.call(
        "takeDepositLegacy", b"", deposit=wide_deposit, expect_success=False
    )
    print("nearctx: >u64 attached_deposit full words pass; legacy UInt64 traps ok")

    self_call = client.call("checkSelfCall", b"")
    self_call_value = NearClient.success_value_bytes(self_call)
    if self_call_value is None or len(self_call_value) < 8:
        raise AssertionError(f"checkSelfCall SuccessValue expected ≥8 bytes, got {self_call_value!r}")
    if NearClient.decode_u64_le(self_call_value, 0) != 1:
        raise AssertionError("checkSelfCall must return 1 for direct self-account transaction")
    if client.view_u64("get") != 1:
        raise AssertionError("checkSelfCall must persist stamped=1")
    print("nearctx: full predecessor == current account self-call gate ok")

    h0 = client.latest_block_height()
    view_h = client.view_u64("height")
    h1 = client.latest_block_height()
    if h0 != h1:
        h0 = h1
        view_h = client.view_u64("height")
        h1 = client.latest_block_height()
        if h0 != h1:
            raise AssertionError(
                f"block height still advancing under sole-client view (h0={h0}, h1={h1})"
            )
    if view_h != h0:
        raise AssertionError(
            f"height() must equal status.latest_block_height ({h0}), got {view_h}"
        )
    print(f"nearctx: height() == latest_block_height ({h0}) ok")

    before = client.latest_block_height()
    res = client.call("stamp", b"")
    after = client.latest_block_height()
    sv = NearClient.success_value_bytes(res)
    if sv is None or len(sv) < 8:
        raise AssertionError(f"stamp SuccessValue expected ≥8 LE bytes, got {sv!r}")
    stamped = NearClient.decode_u64_le(sv, 0)
    stored = client.view_u64("get")
    if stored != stamped:
        raise AssertionError(
            f"get() after stamp must equal SuccessValue ({stamped}), got {stored}"
        )
    if not (before < stamped <= after):
        raise AssertionError(
            f"stamp height {stamped} not in (before={before}, after={after}]"
        )
    print(f"nearctx: stamp() → get()=={stamped} (before={before}, after={after}) ok")

    seconds = client.view_u64("seconds")
    if seconds == 0:
        raise AssertionError("seconds() returned 0; sandbox block_timestamp should be live")
    print(f"nearctx: seconds() == {seconds} ok")

    print("suite NearCtx: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-context: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
