#!/usr/bin/env python3
"""Dynamic storage-usage delta scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-storage-economics: missing env {name}")
    return value


def _call_u64(client: NearClient, method: str) -> int:
    raw = NearClient.success_value_bytes(client.call(method, b""))
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected u64 result, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    client.deploy(Path(_require("PF_NEAR_WASM")))
    client.call("initialize", b"")

    usage0 = client.view_u64("usage")
    usage1 = client.view_u64("usage")
    if usage0 <= 0 or usage1 != usage0:
        raise AssertionError(f"storage usage view was not positive/stable: {usage0}, {usage1}")

    short4 = _call_u64(client, "insertShort4")
    if short4 <= 0:
        raise AssertionError(f"first short-key insert did not grow storage: {short4}")
    replace4 = _call_u64(client, "replaceShort4")
    if replace4 != 0:
        raise AssertionError(f"same-key/same-length replacement changed storage usage: {replace4}")
    if _call_u64(client, "growShort8") != 4:
        raise AssertionError("four-byte value growth did not add exactly four usage bytes")
    if _call_u64(client, "removeShort") != short4 + 4:
        raise AssertionError("short-key removal did not reclaim its measured key/value usage")
    if _call_u64(client, "removeMissing") != 0:
        raise AssertionError("removing an absent key changed storage usage")

    long4 = _call_u64(client, "insertLong4")
    if long4 != short4 + 4:
        raise AssertionError(
            f"four extra active key bytes did not add four usage bytes: {short4}, {long4}"
        )
    if _call_u64(client, "removeLong") != long4:
        raise AssertionError("long-key removal did not reclaim its measured insertion usage")
    if client.view_u64("usage") != usage0:
        raise AssertionError("insert/remove scenes did not return to baseline storage usage")

    print("near-storage-economics: dynamic key/value deltas and reclamation ok")
    print("suite NearStorageEconomics: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage-economics: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
