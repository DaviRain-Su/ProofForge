#!/usr/bin/env python3
"""Counter lifecycle/arithmetic harness against local near-sandbox (engineering only).

Scenes:
  ordinary call/view before initialize fail with exact missing-state panic
  paid pre-initialize mutator fails non-payable before missing-state
  initialize with deposit fails before creating state
  initialize(0) → get()==0
  repeated initialize fails and preserves initialized state
  increment with deposit fails and preserves state
  increment(1) ok → get()==1
  increment overflow (2^64-1) fails; state holds
  get is a view (8-byte LE)
  upgrade to a two-field schema → ordinary entries reject old envelope
  external migration is private; same-account migration converts the exact old key
  transformed fields are visible only with the new exact schema envelope

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM / PF_NEAR_MIGRATION_WASM.
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
    migration_wasm = Path(_require("PF_NEAR_MIGRATION_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: Counter (initialize / increment / overflow / get) ===")
    client.deploy(wasm)

    paid_preinit = client.call(
        "increment", NearClient.encode_u64_le(1), deposit=1, expect_success=False
    )
    if "Method increment doesn't accept deposit" not in repr(paid_preinit):
        raise AssertionError(
            f"paid pre-initialize increment returned the wrong panic: {paid_preinit!r}"
        )
    print("counter: paid pre-initialize increment rejected before lifecycle guard ok")

    preinit_call = client.call(
        "increment", NearClient.encode_u64_le(1), expect_success=False
    )
    if "The contract is not initialized" not in repr(preinit_call):
        raise AssertionError(
            f"pre-initialize increment returned the wrong panic: {preinit_call!r}"
        )
    try:
        client.view_u64("get")
    except NearRpcError as error:
        if "The contract is not initialized" not in repr(error):
            raise AssertionError(
                f"pre-initialize get returned the wrong panic: {error!r}"
            ) from error
    else:
        raise AssertionError("pre-initialize get unexpectedly succeeded")
    if client.view_state_values():
        raise AssertionError("rejected pre-initialize entries created contract state")
    print("counter: pre-initialize call/view rejected + state remains empty ok")

    paid_init = client.call(
        "initialize", NearClient.encode_u64_le(77), deposit=1, expect_success=False
    )
    if "Method initialize doesn't accept deposit" not in repr(paid_init):
        raise AssertionError(f"paid initialize returned the wrong panic: {paid_init!r}")
    print("counter: paid initialize rejected before state creation ok")

    client.call("initialize", NearClient.encode_u64_le(0))
    expected_state_envelope = b"PFNRST01" + bytes.fromhex("ad143be1f1fee08d")
    actual_state_envelope = client.view_state_values().get(b"STATE")
    if actual_state_envelope != expected_state_envelope:
        raise AssertionError(
            "STATE envelope mismatch: "
            f"expected {expected_state_envelope.hex()}, "
            f"got {actual_state_envelope.hex() if actual_state_envelope else None}"
        )
    print("counter: exact versioned STATE schema envelope ok")
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize(0): get() expected 0, got {got}")
    print("counter: initialize(0) → get()==0 ok")

    repeated = client.call(
        "initialize", NearClient.encode_u64_le(99), expect_success=False
    )
    if "The contract has already been initialized" not in repr(repeated):
        raise AssertionError(f"repeated initialize returned the wrong panic: {repeated!r}")
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(
            f"after repeated initialize(99): get() must stay 0, got {got}"
        )
    print("counter: repeated initialize fails + state holds at 0 ok")

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

    paid_increment = client.call(
        "increment", NearClient.encode_u64_le(9), deposit=1, expect_success=False
    )
    if "Method increment doesn't accept deposit" not in repr(paid_increment):
        raise AssertionError(
            f"paid increment returned the wrong panic: {paid_increment!r}"
        )
    got = client.view_u64("get")
    if got != 1:
        raise AssertionError(f"after paid increment: get() must stay 1, got {got}")
    print("counter: paid increment rejected + state holds at 1 ok")

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

    client.deploy(migration_wasm)
    try:
        client.view_u64("get")
    except NearRpcError as error:
        if "The contract state version is incompatible" not in repr(error):
            raise AssertionError(
                f"pre-migration V2 view returned the wrong panic: {error!r}"
            ) from error
    else:
        raise AssertionError("V2 ordinary view accepted the old Counter envelope")
    print("counter: upgraded ordinary view rejected the exact old schema ok")

    attacker = "migration-attacker.test.near"
    client.create_subaccount_with_key(attacker, 10**25)
    rejected = client.call_on(
        client.account_id, "migrate", signer=attacker, expect_success=False
    )
    if "Method migrate is private" not in repr(rejected):
        raise AssertionError(
            f"external migration returned the wrong private panic: {rejected!r}"
        )
    print("counter: external migration rejected by exact private guard ok")

    migrated = client.call("migrate")
    migrated_value = NearClient.success_value_bytes(migrated)
    if migrated_value not in (None, NearClient.encode_u64_le(2)):
        raise AssertionError(
            f"migration returned wrong value bytes: {migrated_value!r}"
        )
    if client.view_u64("get") != 2 or client.view_u64("revisionOf") != 2:
        raise AssertionError("migration did not convert Counter value=2 into V2 revision=2")
    values = client.view_state_values()
    expected_new_envelope = b"PFNRST01" + bytes.fromhex("eefcd2d321ca8f9b")
    if values.get(b"STATE") != expected_new_envelope:
        raise AssertionError(
            "migrated STATE envelope mismatch: "
            f"expected {expected_new_envelope.hex()}, got {values.get(b'STATE')!r}"
        )
    if values.get(b"total") != NearClient.encode_u64_le(2):
        raise AssertionError("migration did not persist transformed total=2")
    if values.get(b"revision") != NearClient.encode_u64_le(2):
        raise AssertionError("migration did not persist revision=2")
    if values.get(b"value") != NearClient.encode_u64_le(2):
        raise AssertionError("migration unexpectedly removed the explicitly retained legacy key")
    print("counter: private old-key conversion + exact new envelope ok")

    repeated_migration = client.call("migrate", expect_success=False)
    if "The contract state version is incompatible" not in repr(repeated_migration):
        raise AssertionError(
            f"repeated migration returned the wrong panic: {repeated_migration!r}"
        )
    client.call("increment", NearClient.encode_u64_le(1))
    if client.view_u64("get") != 3 or client.view_u64("revisionOf") != 2:
        raise AssertionError("post-migration V2 mutation failed")
    print("counter: repeated migration rejected + V2 mutation remains live ok")
    print("suite Counter: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-counter: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
