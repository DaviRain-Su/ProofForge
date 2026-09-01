# wsm-near-lookup-001 — NEAR direct Identity LookupMap64 / LookupSet64 foundation

Status: done

Depends on: [wsm-near-vector-001](wsm-near-vector-001.md)

## Scope

Add fixed-width direct lookup foundations over bounded raw storage, following current
`near-sdk-rs 5.29.0` `store::*` default `Identity` key policy:

- `DirectLookupMap64` key: four-byte compile-time prefix followed by standalone Borsh `UInt64`;
- map value: standalone Borsh `UInt64`;
- `DirectLookupSet64` key: the same prefix/key recipe;
- set value: the exact empty byte string, not a Borsh unit marker.

Every map/set/vector instance and raw key remains caller-namespaced. SHA-256 and Keccak key
policies are absent. A shared store codec owns `Prefix4`, fixed UInt32/UInt64 suffix recipes,
Borsh UInt64 values, and exact-width result decoding.

The map is deliberately immediate-write. Its durable bytes are compatible with the Rust Identity
layout, but mutation timing, gas, and same-invocation visibility differ from Rust `LookupMap`,
which caches modifications until `flush`/`Drop`. The set's immediate persistence matches the Rust
policy, while this scalar compiler surface returns raw 0/1 storage words instead of Rust `bool`.
`put`/`remove` do not return the old map value. Generic codecs, custom hashers, borrowed keys,
references, entries, iteration, metadata, and collection cardinality are outside this slice.

The slice also teaches scalar-let extraction to recognize nested `pf_inline` NEAR effects. Without
that compiler rule, an SDK `put`/`remove` result consumed by a state transition could silently lose
the host effect even though a direct `ResultBuffer` call worked.

## Verification

- `Tests.NearLookupSpec` pins exact 12-byte Identity keys, map Borsh values, empty set values,
  read/has/write/remove effects, per-method WAT emission, bit codecs, and canonical digest.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearLookup` fixture.
- `runtime-tests/near/lookup.sh` deploys to near-sandbox 2.13.0 and verifies missing values,
  insert/replace status, exact `MAP1 || u64_le(key)` map bytes, exact empty set values,
  namespace separation, duplicate insertion, removal/reclamation, zero-value presence versus
  absence, and maximum-UInt64 lookup.
- The fixture fixes the mutating map key to 7 because NEAR v0 currently permits at most one
  UInt64 method parameter; multi-parameter Borsh ABI is not smuggled into this collection slice.

## Next

The ProofForge-owned bounded persistent Queue landed in
[wsm-near-queue-001](wsm-near-queue-001.md). Next compose bounded Identity IterableMap/IterableSet
without claiming near-sdk-rs cache/`Drop` timing.
