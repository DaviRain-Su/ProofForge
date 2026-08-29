# wsm-near-iterable-001 — NEAR bounded Identity IterableMap64 / IterableSet64

Status: done

Depends on: [wsm-near-queue-001](wsm-near-queue-001.md)

## Scope

Add fixed-capacity `UInt64` iterable map/set foundations matching current near-sdk-rs 5.29.0 when
the caller explicitly selects the `Identity` key hasher and a three-byte base prefix `P`:

- vector namespace `P || 'v'`, key suffix `u32_le(index)`, and Borsh `UInt64` key/member value;
- lookup namespace `P || 'm'` and Identity `u64_le(key/member)` suffix;
- map lookup payload `u64_le(value) || u32_le(index)`;
- set lookup payload `u32_le(index)`;
- capacity is compile-time `1..64`; logical length remains ordinary caller state until N9;
- fresh insert appends, map replacement preserves its index, and duplicate set insert is a no-op;
- removal uses exact swap-remove order, repairs the moved lookup index, and reclaims the target
  lookup plus obsolete last vector slot;
- missing or malformed lookup/tail records and out-of-capacity indices fail before writes;
  swap-remove also verifies the moved tail's reverse index before mutation.

The SDK accepts the derived `Prefix4` vector/lookup tags so each storage operation remains within
the current extractor's statically bounded frame. `Prefix3.vectorTag` and `lookupTag` pin the exact
Rust namespace derivation. The fixture packs two UInt32 test words into its one UInt64 `mapPut`
argument only because the current NEAR v0 ABI supports one scalar method parameter; durable SDK
keys and values remain full UInt64 encodings.

All writes are immediate and nearcore transaction rollback supplies failure atomicity. This does
not claim compatibility with default Sha256 keys, Rust cache/flush/Drop timing, generic Borsh
types, alternate hashers, iterators, entries, drains, or collection metadata serialization.

## Compiler prerequisite

Swap-remove must retain target index, moved key/member, and moved value across later storage reads
that replace the one active result buffer. Scalar-local extraction now recursively recognizes
composites containing mutable NEAR storage-result leaves and materializes them before a later
effect. The extraction test pins these locals so future optimization cannot silently reread a
different result register.

## Verification

- `Tests.NearIterableSpec` pins prefix derivation, exact vector/lookup keys and payloads, bounds,
  all read/write/remove/has effect sequences, scalar snapshots, per-method WAT, and digest.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearIterable` fixture.
- `runtime-tests/near/iterable.sh` deploys to near-sandbox 2.13.0 and verifies exact durable map/set
  bytes, absence versus index zero, replacement and duplicate behavior, capacity rollback,
  swap-remove order, moved-index/value repair, key reclamation, and malformed-record fail-closed
  rollback.

## Next

Begin N7 with a closed static cross-contract function call carrying explicit gas and attached
deposit. Promise chaining/results and callbacks remain separate slices.
