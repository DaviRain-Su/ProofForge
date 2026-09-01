#!/usr/bin/env python3
"""Bounded arbitrary-binary storage scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


BINARY_KEY = b"\x00\xff\x01"
MAXIMUM_IDENTITY_KEY = b"PFID" + (64).to_bytes(4, "little") + bytes(range(64))


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-storage: missing env {name}")
    return value


def _call_u64(client: NearClient, method: str, args: bytes = b"") -> int:
    result = client.call(method, args)
    raw = NearClient.success_value_bytes(result)
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected 8-byte SuccessValue, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def _bytes(client: NearClient, length: int) -> bytes:
    return bytes(
        client.view_u64("readByte", NearClient.encode_u64_le(index))
        for index in range(length)
    )


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearStorage (bounded binary KV / explicit host status) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    if client.view_u64("has") != 0 or client.view_u64("readStatus") != 0:
        raise AssertionError("missing binary key must have has/read status 0")
    if client.view_u64("readLength") != 0 or _bytes(client, 2) != b"\x00\x00":
        raise AssertionError("missing read must expose length 0 and zero inactive bytes")
    print("near-storage: absent status/length and inactive-byte zeroing ok")

    first = b"\x11\x00\xff\x02"
    if _call_u64(client, "put", NearClient.borsh_bytes(first)) != 0:
        raise AssertionError("first write must return inserted status 0")
    if client.view_u64("has") != 1 or client.view_u64("readStatus") != 1:
        raise AssertionError("present binary key must have has/read status 1")
    if client.view_u64("readLength") != len(first) or _bytes(client, 8) != first + b"\x00" * 4:
        raise AssertionError("bounded read did not copy exact value and zero inactive lanes")
    if client.view_u64("staleByteAfterMiss") != 0:
        raise AssertionError("status-0 read exposed bytes from a preceding hit in the same invocation")
    if client.view_state_values().get(BINARY_KEY) != first:
        raise AssertionError("near state does not contain the byte-exact NUL/0xff key/value")
    print("near-storage: binary key, inserted/read status, and same-call stale isolation ok")

    second = b"\x22"
    if _call_u64(client, "putOldFirst", NearClient.borsh_bytes(second)) != first[0]:
        raise AssertionError("replacement did not expose the first evicted byte")
    if client.view_u64("readLength") != 1 or _bytes(client, 2) != second + b"\x00":
        raise AssertionError("replacement value readback mismatch")
    print("near-storage: replaced status register copied evicted bytes ok")

    if _call_u64(client, "put", NearClient.borsh_bytes(b"")) != 1:
        raise AssertionError("present key replaced by empty value must return status 1")
    if client.view_u64("has") != 1 or client.view_u64("readStatus") != 1:
        raise AssertionError("present-empty value must remain distinguishable from absent")
    if client.view_u64("readLength") != 0 or _bytes(client, 1) != b"\x00":
        raise AssertionError("present-empty read must have length 0 and zero bytes")
    print("near-storage: present-empty differs from absent ok")

    full = bytes(range(1, 9))
    if _call_u64(client, "put", NearClient.borsh_bytes(full)) != 1:
        raise AssertionError("full replacement must return status 1")
    if client.view_u64("readSmallStatus") != 1:
        raise AssertionError("oversized bounded read must preserve present status 1")
    if client.view_u64("readSmallLength") != 8 or client.view_u64("readSmallFits") != 0:
        raise AssertionError("oversized bounded read must expose actual length and fits 0")
    if client.view_u64("readSmallByte", NearClient.encode_u64_le(0)) != 0:
        raise AssertionError("oversized uncopied result bytes must read as zero")
    if client.view_state_values().get(BINARY_KEY) != full:
        raise AssertionError("oversized read must not mutate the stored value")
    print("near-storage: oversized register result reports status/length/fits without copy ok")

    if _call_u64(client, "removeOldFirst") != full[0]:
        raise AssertionError("remove did not expose the first removed byte")
    if client.view_u64("has") != 0 or BINARY_KEY in client.view_state_values():
        raise AssertionError("binary key remained after remove")
    if _call_u64(client, "remove") != 0:
        raise AssertionError("second remove must return absent status 0")
    print("near-storage: removed value and absent remove status ok")

    empty_key_value = b"emptykey"
    if _call_u64(client, "putEmptyKey", NearClient.borsh_bytes(empty_key_value)) != 0:
        raise AssertionError("first empty-key write must return inserted status 0")
    if client.view_u64("hasEmptyKey") != 1:
        raise AssertionError("empty key must be present")
    if client.view_state_values().get(b"") != empty_key_value:
        raise AssertionError("near state does not contain the exact empty key/value")
    print("near-storage: zero-length key accepted and persisted ok")

    maximum_value = b"key72"
    if _call_u64(client, "putMaximumKey", NearClient.borsh_bytes(maximum_value)) != 0:
        raise AssertionError("first exact-72-byte key write must return inserted status 0")
    if client.view_u64("hasMaximumKey") != 1:
        raise AssertionError("exact-72-byte key must be present")
    actual = bytes(
        client.view_u64("readMaximumKeyByte", NearClient.encode_u64_le(index))
        for index in range(len(maximum_value))
    )
    if actual != maximum_value:
        raise AssertionError(f"exact-72-byte key value mismatch: {actual!r}")
    if client.view_state_values().get(MAXIMUM_IDENTITY_KEY) != maximum_value:
        raise AssertionError("near state does not contain the exact active 72-byte key")
    if _call_u64(client, "removeMaximumKey") != 1:
        raise AssertionError("exact-72-byte key removal must return present status 1")
    if client.view_u64("hasMaximumKey") != 0 or MAXIMUM_IDENTITY_KEY in client.view_state_values():
        raise AssertionError("exact-72-byte key remained after removal")
    print("near-storage: exact 72-byte key write/read/remove and reclamation ok")
    print("suite NearStorage: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-storage: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
