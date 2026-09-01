#!/usr/bin/env python3
"""Canonical Borsh and specialized JSON-u128 output scenes against local near-sandbox."""

from __future__ import annotations

import base64
import json
import os
import struct
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-output: missing env {name}")
    return value


def _expect(client: NearClient, method: str, args: bytes, expected: bytes) -> None:
    got = client.view(method, args)
    if got != expected:
        raise AssertionError(
            f"{method}({args.hex()}): expected {expected.hex()}, got {got.hex()}"
        )


def _expect_failure(client: NearClient, method: str, args: bytes, scene: str) -> None:
    try:
        client.view(method, args)
    except NearRpcError:
        print(f"near-output: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    unit_wasm = Path(_require("PF_NEAR_UNIT_WASM"))
    mutation_wasm = Path(_require("PF_NEAR_MUTATION_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearOutput (canonical Borsh + JSON u128) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    _expect(client, "get", b"", NearClient.encode_u64_le(0))
    _expect(client, "emptyBytes", b"", NearClient.borsh_bytes(b""))
    _expect(client, "staticBytes", b"", NearClient.borsh_bytes(b"\x00\x01\xff"))
    _expect(client, "staticString", b"", NearClient.borsh_bytes("😀".encode()))
    expected_values = struct.pack("<IHHH", 3, 1, 513, 65535)
    _expect(client, "staticValues", b"", expected_values)
    print("near-output: empty/bytes/String/UInt16[] exact Borsh bytes ok")

    json_u128 = {
        "jsonU128Zero": 0,
        "jsonU128Two64": 1 << 64,
        "jsonU128Two64PlusOne": (1 << 64) + 1,
        "jsonU128Asymmetric": (1 << 64) + 2,
        "jsonU128Max": (1 << 128) - 1,
    }
    for method, value in json_u128.items():
        expected = f'"{value}"'.encode("ascii")
        _expect(client, method, b"", expected)
        if not (3 <= len(expected) <= 41):
            raise AssertionError(f"{method}: JSON u128 output length escaped 3..41")
    print("near-output: zero/high/mixed/max u128 exact quoted decimal bytes ok")

    hashes = {
        "jsonBase64Hash32": bytes(range(32)),
        "jsonBase64Hash32Zero": bytes(32),
        "jsonBase64Hash32Max": b"\xff" * 32,
    }
    before_hash_views = client.view_state_values()
    for method, raw in hashes.items():
        expected = b'"' + base64.b64encode(raw) + b'"'
        _expect(client, method, b"", expected)
        if len(expected) != 46 or expected[44:45] != b"=" or expected[45:] != b'"':
            raise AssertionError(f"{method}: Base64 quote/padding geometry changed")
        if b"\\" in expected or b"\r" in expected or b"\n" in expected:
            raise AssertionError(f"{method}: Base64 JSON string was unnecessarily escaped")
        if base64.b64decode(expected[1:-1], validate=True) != raw:
            raise AssertionError(f"{method}: independent Base64 round trip changed packed bytes")
    if client.view_state_values() != before_hash_views:
        raise AssertionError("Base64 hash output view changed contract state")
    print("near-output: exact 32-byte RFC4648 STANDARD Base64 JSON string ok")

    def metadata_wire(
        name: str = "",
        symbol: str = "",
        icon: str | None = None,
        reference: str | None = None,
        reference_hash: bytes | None = None,
        decimals: int = 0,
    ) -> bytes:
        payload = {
            "spec": "ft-1.0.0",
            "name": name,
            "symbol": symbol,
            "icon": icon,
            "reference": reference,
            "reference_hash": (
                base64.b64encode(reference_hash).decode("ascii")
                if reference_hash is not None
                else None
            ),
            "decimals": decimals,
        }
        return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")

    _expect(client, "jsonMetadataEscaped", b"", metadata_wire(
        'A"\\\0é😀', "FT", "icon\n", "参考", bytes(range(32)), 9
    ))
    max_metadata = metadata_wire(
            "\0" * 64,
            "\0" * 16,
            "\0" * 256,
            "\0" * 128,
            b"\xff" * 32,
            255,
    )
    _expect(client, "jsonMetadataMax", b"", max_metadata)
    _expect(client, "jsonMetadataReferenceOnly", b"", metadata_wire(reference="", decimals=10))
    _expect(client, "jsonMetadataHashOnly", b"", metadata_wire(reference_hash=bytes(32), decimals=99))
    _expect(client, "jsonMetadataBothEmpty", b"",
        metadata_wire(icon="", reference="", reference_hash=bytes(32), decimals=100))
    before_metadata_views = client.view_state_values()
    for decimals in (0, 9, 10, 99, 100, 255):
        _expect(client, "jsonMetadataDecimals", NearClient.encode_u64_le(decimals),
            metadata_wire(decimals=decimals))
    if len(max_metadata) != 2929:
        raise AssertionError(
            f"max metadata wire expected exact 2929 bytes, got {len(max_metadata)}"
        )
    for method, args, scene in (
        ("jsonMetadataNameLength", NearClient.encode_u64_le(65), "name length 65"),
        ("jsonMetadataSymbolLength", NearClient.encode_u64_le(17), "symbol length 17"),
        ("jsonMetadataIconLength", NearClient.encode_u64_le(257), "icon length 257"),
        ("jsonMetadataReferenceLength", NearClient.encode_u64_le(129), "reference length 129"),
        ("jsonMetadataPresence", NearClient.encode_u64_le(2), "option presence above one"),
        ("jsonMetadataInactiveByte", b"", "inactive partial-word byte"),
        ("jsonMetadataNoneStaleHash", b"", "None hash stale word"),
        ("jsonMetadataMalformedUtf8", b"", "malformed UTF-8"),
        ("jsonMetadataOverlongUtf8", b"", "overlong UTF-8"),
        ("jsonMetadataSurrogateUtf8", b"", "surrogate UTF-8"),
        ("jsonMetadataAboveUnicodeUtf8", b"", "above-Unicode UTF-8"),
        ("jsonMetadataTruncatedUtf8", b"", "truncated UTF-8"),
        ("jsonMetadataNoneStaleIcon", b"", "None icon stale byte"),
        ("jsonMetadataNoneStaleReference", b"", "None reference stale byte"),
        ("jsonMetadataDecimals", NearClient.encode_u64_le(256), "decimals above 255"),
    ):
        _expect_failure(
            client,
            method,
            args,
            f"bounded metadata {scene}",
        )
    # A late failed frame cannot leak staged bytes into the next successful view.
    _expect(client, "jsonMetadataEscaped", b"", metadata_wire(
        'A"\\\0é😀', "FT", "icon\n", "参考", bytes(range(32)), 9))
    _expect_failure(
        client,
        "jsonMetadataNoneStaleHash",
        b"",
        "bounded metadata stale isolation failure",
    )
    _expect(client, "jsonMetadataDecimals", NearClient.encode_u64_le(0), metadata_wire())
    if client.view_state_values() != before_metadata_views:
        raise AssertionError("bounded metadata output view changed contract state")
    print("near-output: bounded metadata options/UTF-8/Base64/decimals/max/fail-closed matrix ok")

    for raw in (b"", b"x", bytes(range(8))):
        wire = NearClient.borsh_bytes(raw)
        _expect(client, "echoBytes", wire, wire)
    for text in ("A", "é", "😀"):
        wire = NearClient.borsh_bytes(text.encode())
        _expect(client, "echoString", wire, wire)
    print("near-output: bounded input/output round trips ok")

    _expect(
        client,
        "stringWithByte",
        NearClient.encode_u64_le(ord("A")),
        NearClient.borsh_bytes(b"A"),
    )
    _expect_failure(
        client,
        "stringWithByte",
        NearClient.encode_u64_le(0x80),
        "malformed UTF-8 output",
    )

    _expect(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(0),
        NearClient.borsh_bytes(b""),
    )
    _expect(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(8),
        NearClient.borsh_bytes(bytes(range(1, 9))),
    )
    _expect_failure(
        client,
        "bytesWithLength",
        NearClient.encode_u64_le(9),
        "output length above capacity",
    )
    print("near-output: output UTF-8 and capacity guards ok")

    mutation_account = "u128-mutation.test.near"
    client.create_subaccount_with_key(mutation_account, 10**27)
    client.deploy_to(mutation_account, mutation_wasm)
    client.call_on(mutation_account, "initialize", b"", signer=mutation_account)
    first = client.call_on(
        mutation_account,
        "commitAsymmetric",
        NearClient.encode_u64_le(37),
        signer=mutation_account,
    )
    expected_result = f'"{(1 << 64) + 2}"'.encode("ascii")
    if NearClient.success_value_bytes(first) != expected_result:
        raise AssertionError("mutating u128 result lost independent asymmetric limbs")
    if client.view_u64_on(mutation_account, "get") != 37 or client.view_u64_on(
        mutation_account, "right"
    ) != 0x8877665544332211:
        raise AssertionError("mutating u128 result did not persist both state fields first")
    client.call_on(
        mutation_account,
        "commitAsymmetric",
        NearClient.encode_u64_le(0),
        signer=mutation_account,
        expect_success=False,
    )
    if client.view_u64_on(mutation_account, "get") != 37:
        raise AssertionError("failed mutating u128 result changed state")
    repeated = client.call_on(
        mutation_account,
        "commitAsymmetric",
        NearClient.encode_u64_le(44),
        signer=mutation_account,
    )
    if NearClient.success_value_bytes(repeated) != expected_result or client.view_u64_on(
        mutation_account, "get"
    ) != 44:
        raise AssertionError("repeated mutating u128 result aliased state and result destinations")
    print("near-output: mutating quoted u128 persisted two fields, returned once, and rolled back")

    print("=== suite: NearJsonUnitOutput (mutating JSON null) ===")
    client.deploy(unit_wasm)
    # NearOutput and this fixture deliberately share the one-slot `marker` state schema, so the
    # redeployed contract consumes the already initialized zero state instead of reinitializing.
    success = client.call("setMarker", NearClient.encode_u64_le(37))
    returned = NearClient.success_value_bytes(success)
    if returned != b"null":
        raise AssertionError(f"setMarker SuccessValue expected exact b'null', got {returned!r}")
    _expect(client, "get", b"", NearClient.encode_u64_le(37))
    failed = client.call("setMarker", NearClient.encode_u64_le(0), expect_success=False)
    if NearClient.success_value_bytes(failed) is not None:
        raise AssertionError("failed Unit mutation unexpectedly returned a SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(37))
    success = client.call("setMarker", NearClient.encode_u64_le(99))
    if NearClient.success_value_bytes(success) != b"null":
        raise AssertionError("second Unit mutation did not return exact JSON null")
    _expect(client, "get", b"", NearClient.encode_u64_le(99))
    print("near-output: exact null bytes, state persistence, repeated calls, and rollback ok")

    success = client.call("setMarkerVoid", NearClient.encode_u64_le(123))
    if NearClient.success_value_bytes(success) != b"":
        raise AssertionError("void mutation did not return exact empty SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(123))
    failed = client.call("setMarkerVoid", NearClient.encode_u64_le(0), expect_success=False)
    if NearClient.success_value_bytes(failed) is not None:
        raise AssertionError("failed void mutation unexpectedly returned a SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(123))
    success = client.call("setMarkerVoid", NearClient.encode_u64_le(456))
    if NearClient.success_value_bytes(success) != b"":
        raise AssertionError("repeated void mutation did not return exact empty SuccessValue")
    _expect(client, "get", b"", NearClient.encode_u64_le(456))
    print("near-output: exact empty return, state persistence, repeated calls, and rollback ok")
    print("suite NearOutput: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-output: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
