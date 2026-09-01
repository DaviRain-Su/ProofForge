#!/usr/bin/env python3
"""Callback-result count and out-of-range host behavior against near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-promise-result: missing env {name}")
    return value


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearPromiseResult (bounded callback-result substrate) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    count_call = client.call("resultsCount")
    count_bytes = NearClient.success_value_bytes(count_call)
    if count_bytes != NearClient.encode_u64_le(0):
        raise AssertionError(
            f"ordinary call promise_results_count expected 0, got {count_bytes!r}"
        )
    if client.view_u64("get") != 0:
        raise AssertionError("resultsCount did not persist the exact zero count")
    print("near-promise-result: ordinary transaction has zero callback inputs")

    client.call("resultStatus", expect_success=False)
    if client.view_u64("get") != 0:
        raise AssertionError("out-of-range promise_result changed persistent state")
    print("near-promise-result: result index outside count aborts and rolls back")
    print("suite NearPromiseResult: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-promise-result: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
