#!/usr/bin/env python3
"""Exact Borsh-u128 storage-value scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError

KEY = b"TOK1"
FALLBACK = (0xFEDCBA9876543210, 0x0123456789ABCDEF)


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-token-storage: missing env {name}")
    return value


def _call_u64(client: NearClient, method: str, args: bytes = b"") -> int:
    raw = NearClient.success_value_bytes(client.call(method, args))
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected u64 result, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def _decoded(client: NearClient) -> tuple[int, int]:
    return client.view_u64("readW0"), client.view_u64("readW1")


def main() -> None:
    client = NearClient(_require("PF_NEAR_RPC"), Path(_require("PF_NEAR_HOME")))
    client.deploy(Path(_require("PF_NEAR_WASM")))
    client.call("initialize", b"")

    if client.view_u64("has") != 0 or client.view_u64("readStatus") != 0:
        raise AssertionError("missing value status mismatch")
    if client.view_u64("readLength") != 0 or client.view_u64("readFits") != 1:
        raise AssertionError("missing value must have length 0 and fit")
    if _decoded(client) != FALLBACK:
        raise AssertionError("missing value did not return both fallback limbs")

    mixed = (0x0102030405060708, 0x1112131415161718)
    if _call_u64(client, "putMixed") != 0 or _decoded(client) != mixed:
        raise AssertionError("mixed-limb insert/decode mismatch")
    expected = mixed[0].to_bytes(8, "little") + mixed[1].to_bytes(8, "little")
    if client.view_state_values().get(KEY) != expected:
        raise AssertionError("mixed token was not stored as exact 16-byte LE")
    if client.view_u64("staleAfterMissW0") != FALLBACK[0]:
        raise AssertionError("missing read exposed a preceding hit register")

    maximum = (2**64 - 1, 2**64 - 1)
    if _call_u64(client, "putMax") != 1 or client.view_u64("get") != 1:
        raise AssertionError("replacement status was not committed after storage write")
    if _decoded(client) != maximum or client.view_state_values().get(KEY) != b"\xff" * 16:
        raise AssertionError("maximum u128 roundtrip mismatch")

    if _call_u64(client, "putShort") != 1:
        raise AssertionError("short malformed replacement status mismatch")
    if client.view_u64("readStatus") != 1 or client.view_u64("readLength") != 8:
        raise AssertionError("short malformed value descriptor mismatch")
    if client.view_u64("readFits") != 1 or _decoded(client) != FALLBACK:
        raise AssertionError("short value must fit but fail exact-length decode")

    oversized = bytes(range(20))
    if _call_u64(client, "putOversized", NearClient.borsh_bytes(oversized)) != 1:
        raise AssertionError("oversized replacement status mismatch")
    if client.view_u64("readStatus") != 1 or client.view_u64("readLength") != 20:
        raise AssertionError("oversized descriptor lost status/actual length")
    if client.view_u64("readFits") != 0 or _decoded(client) != FALLBACK:
        raise AssertionError("oversized uncopied value did not return fallback")
    if client.view_state_values().get(KEY) != oversized:
        raise AssertionError("failed decode mutated oversized durable bytes")

    if _call_u64(client, "putZero") != 1 or _decoded(client) != (0, 0):
        raise AssertionError("zero token replacement mismatch")
    if client.view_u64("has") != 1 or client.view_state_values().get(KEY) != b"\0" * 16:
        raise AssertionError("stored zero was confused with absence")

    if _call_u64(client, "remove") != 1 or KEY in client.view_state_values():
        raise AssertionError("present remove did not reclaim key")
    if _call_u64(client, "remove") != 0 or _decoded(client) != FALLBACK:
        raise AssertionError("absent remove/missing fallback mismatch")
    print("near-token-storage: exact limbs, malformed bounds, stale isolation and removal ok")
    print("suite NearTokenStorage: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-token-storage: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
