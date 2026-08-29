#!/usr/bin/env python3
"""Counter four-scene harness against local near-sandbox (engineering only).

Scenes:
  initialize(0) → get()==0
  increment(1) ok → get()==1
  increment overflow (2^64-1) fails; state holds
  get is a view (8-byte LE)

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-counter: missing env {name}")
    return v


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: Counter (initialize / increment / overflow / get) ===")
    client.deploy(wasm)

    client.call("initialize", NearClient.encode_u64_le(0))
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize(0): get() expected 0, got {got}")
    print("counter: initialize(0) → get()==0 ok")

    inc = client.call("increment", NearClient.encode_u64_le(1))
    sv = NearClient.success_value_bytes(inc)
    if sv is not None and len(sv) >= 8:
        ret = NearClient.decode_u64_le(sv, 0)
        if ret != 1:
            raise AssertionError(f"increment(1) SuccessValue expected 1, got {ret}")
        print(f"counter: increment(1) SuccessValue=={ret} ok")
    got = client.view_u64("get")
    if got != 1:
        raise AssertionError(f"after increment(1): get() expected 1, got {got}")
    print("counter: get()==1 ok")

    max_u64 = (1 << 64) - 1
    client.call("increment", NearClient.encode_u64_le(max_u64), expect_success=False)
    got = client.view_u64("get")
    if got != 1:
        raise AssertionError(f"after overflow increment: get() must stay 1, got {got}")
    print("counter: overflow increment fails + state holds at 1 ok")

    client.call("increment", NearClient.encode_u64_le(1))
    got = client.view_u64("get")
    if got != 2:
        raise AssertionError(f"after post-overflow increment(1): get() expected 2, got {got}")
    print("counter: post-overflow increment(1) → get()==2 ok")
    print("suite Counter: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-counter: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
