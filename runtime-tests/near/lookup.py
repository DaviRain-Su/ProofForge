#!/usr/bin/env python3
"""Direct Identity LookupMap/LookupSet scenes against local near-sandbox."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


MAP_PREFIX = b"MAP1"
SET_PREFIX = b"SET1"
MAP_KEY = 7


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-lookup: missing env {name}")
    return value


def _key(prefix: bytes, value: int) -> bytes:
    return prefix + value.to_bytes(8, "little")


def _call_u64(client: NearClient, method: str, value: int | None = None) -> int:
    args = b"" if value is None else NearClient.encode_u64_le(value)
    result = client.call(method, args)
    raw = NearClient.success_value_bytes(result)
    if raw is None or len(raw) < 8:
        raise AssertionError(f"{method}: expected 8-byte SuccessValue, got {raw!r}")
    return NearClient.decode_u64_le(raw, 0)


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearLookup (direct Identity LookupMap64 / LookupSet64) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    if client.view_u64("mapHas", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("missing map key must not be present")
    if client.view_u64("mapGet", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("missing map key must decode to the explicit fallback")
    if client.view_u64("setHas", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("missing set member must not be present")
    print("near-lookup: missing map/set status and map fallback ok")

    first = 0x0102030405060708
    if _call_u64(client, "mapPut", first) != 0:
        raise AssertionError("first map put must return inserted status 0")
    if client.view_u64("mapHas", NearClient.encode_u64_le(MAP_KEY)) != 1:
        raise AssertionError("inserted map key must be present")
    if client.view_u64("mapGet", NearClient.encode_u64_le(MAP_KEY)) != first:
        raise AssertionError("map get did not decode the first Borsh UInt64")
    state = client.view_state_values()
    expected_map_key = _key(MAP_PREFIX, MAP_KEY)
    if state.get(expected_map_key) != NearClient.encode_u64_le(first):
        raise AssertionError("map did not persist prefix || Borsh-u64 key/value bytes")
    print("near-lookup: exact Identity map key and Borsh-u64 value ok")

    replacement = 0x8877665544332211
    if _call_u64(client, "mapPut", replacement) != 1:
        raise AssertionError("replacement map put must return replaced status 1")
    if client.view_u64("mapGet", NearClient.encode_u64_le(MAP_KEY)) != replacement:
        raise AssertionError("replacement map value was not immediately visible")
    if client.view_state_values().get(expected_map_key) != NearClient.encode_u64_le(replacement):
        raise AssertionError("replacement map value bytes mismatch")
    print("near-lookup: immediate map replacement and raw status ok")

    member = 0xFFEEDDCCBBAA0099
    if _call_u64(client, "setInsert", member) != 0:
        raise AssertionError("first set insert must return raw inserted status 0")
    if _call_u64(client, "setInsert", member) != 1:
        raise AssertionError("duplicate set insert must return raw replaced status 1")
    if client.view_u64("setHas", NearClient.encode_u64_le(member)) != 1:
        raise AssertionError("inserted set member must be present")
    state = client.view_state_values()
    expected_set_key = _key(SET_PREFIX, member)
    if expected_set_key not in state or state[expected_set_key] != b"":
        raise AssertionError("set member must persist with an exact empty byte value")
    if expected_set_key == expected_map_key:
        raise AssertionError("map and set prefixes did not separate keyspaces")
    print("near-lookup: exact set key, empty value, duplicate status, and namespace split ok")

    if _call_u64(client, "setRemove", member) != 1:
        raise AssertionError("present set remove must return status 1")
    if _call_u64(client, "setRemove", member) != 0:
        raise AssertionError("absent set remove must return status 0")
    if expected_set_key in client.view_state_values():
        raise AssertionError("set remove did not reclaim its durable key")

    if _call_u64(client, "mapRemove") != 1:
        raise AssertionError("present map remove must return status 1")
    if _call_u64(client, "mapRemove") != 0:
        raise AssertionError("absent map remove must return status 0")
    if expected_map_key in client.view_state_values():
        raise AssertionError("map remove did not reclaim its durable key")
    if client.view_u64("mapGet", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("removed map key did not return the explicit fallback")
    print("near-lookup: map/set removal status and key reclamation ok")

    if _call_u64(client, "mapPut", 0) != 0:
        raise AssertionError("zero-valued map entry must be inserted into an absent slot")
    if client.view_u64("mapHas", NearClient.encode_u64_le(MAP_KEY)) != 1:
        raise AssertionError("zero-valued map entry must remain distinguishable from absence")
    if client.view_u64("mapGet", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("zero-valued map entry did not decode to zero")
    if _call_u64(client, "mapRemove") != 1:
        raise AssertionError("zero-valued present map entry must remove with status 1")
    if client.view_u64("mapHas", NearClient.encode_u64_le(MAP_KEY)) != 0:
        raise AssertionError("zero-valued map key remained after removal")
    print("near-lookup: zero-valued entry remains distinct from absence through has-key ok")

    maximum = (1 << 64) - 1
    if client.view_u64("mapHas", NearClient.encode_u64_le(maximum)) != 0:
        raise AssertionError("maximum UInt64 map key aliased another encoded key")
    if client.view_u64("setHas", NearClient.encode_u64_le(maximum)) != 0:
        raise AssertionError("maximum UInt64 set member aliased another encoded key")
    print("near-lookup: full-width UInt64 identity key path ok")
    print("suite NearLookup: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-lookup: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
