# wsm-near-vector-001 — NEAR bounded direct-write Vector64 foundation

Status: done

Depends on: [wsm-near-storage-001](wsm-near-storage-001.md)

## Scope

Add `Near.Sdk.Store.DirectVector64`, a compiler-bounded 1..64 `UInt64` persistent-vector
foundation composed over raw storage. `Prefix4` is a compile-time four-byte namespace. Every
element uses the exact current `near_sdk::store::Vector` bare-prefix recipe:

- key: four prefix bytes followed by `u32_le(index)`;
- value: standalone eight-byte little-endian Borsh `UInt64`, without a length tag.

Bounds are checked while the source index is still UInt64, before its low 32 bits become the key
suffix. Distinct valid Prefix4 values therefore have disjoint element keys within this collection
family. Prefixes must additionally stay disjoint from raw keys and compiler ASCII state-field
keys.

The implementation is explicitly direct-write: raw writes/removes happen immediately and remain
transaction-atomic under nearcore rollback. It does not simulate Rust `IndexMap` caching or hidden
`Drop` flush behavior. Logical length stays in an ordinary ProofForge state field until the NEAR
`STATE` lifecycle exists. Consequently this is element key/value layout compatibility, not a claim
of complete `near_sdk::store::Vector`: metadata serialization, generic `T`, iterators, cache/Drop,
and the full method surface remain absent.

The slice also closes two compiler prerequisites exposed by a real collection consumer:

- NEAR WAT now renders UInt64 bit operations/shifts used by LE codecs;
- source scalar locals survive across NEAR effects, and branch lowering no longer discards a raw
  storage effect that precedes a state transition.

## Verification

- `Tests.NearVectorSpec` pins capacity/prefix laws, exact key/value bytes, branch-contained
  read/write/remove extraction, scalar-local preservation, bitwise WAT, and canonical digest.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearVector` fixture.
- `runtime-tests/near/vector.sh` deploys to near-sandbox 2.13.0 and checks empty bounds/rollback,
  exact `VEC1 || u32_le(index)` state keys, Borsh-u64 values, get/set/push/pop, reclamation,
  capacity rollback, and rejection of a large index before u32 narrowing.

## Next

Build bounded direct LookupMap/LookupSet policies over the same key/value recipes, then specify a
bounded Queue. Full Rust Vector metadata belongs with N9 `STATE` serialization/versioning rather
than a second ad-hoc length key.
