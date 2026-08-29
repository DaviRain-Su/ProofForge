#!/usr/bin/env python3
"""NearCtx sandbox scenes for Runtime host reads (engineering only).

Scenes:
  initialize(0) → get()==0
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

    print("=== suite: NearCtx (height / stamp / seconds) ===")
    client.deploy(wasm)

    client.call("initialize", NearClient.encode_u64_le(0))
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize(0): get() expected 0, got {got}")
    print("nearctx: initialize(0) → get()==0 ok")

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
