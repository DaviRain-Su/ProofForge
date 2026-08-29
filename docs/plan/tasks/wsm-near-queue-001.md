# wsm-near-queue-001 — ProofForge bounded persistent NEAR Queue64

Status: done

Depends on: [wsm-near-lookup-001](wsm-near-lookup-001.md)

## Scope

Add `Near.Sdk.Store.DirectQueue64`, a ProofForge-owned fixed-capacity `UInt64` FIFO ring over the
direct raw-storage foundation. Current near-sdk-rs `store::*` exports no Queue, so the type does
not claim Rust SDK collection compatibility.

- capacity is compile-time and restricted to `1..64`;
- durable slots reuse the direct Vector bytes: `Prefix4 || u32_le(physicalIndex)` and standalone
  Borsh `UInt64` values;
- caller-owned `head` and `length` remain ordinary ProofForge state fields until N9 `STATE`;
- canonical empty metadata is `head = length = 0`;
- malformed `head`/`length`, full pushes, empty pops, and inactive offsets fail closed before key
  construction;
- ring arithmetic uses one bounded compare/subtract wrap, never dynamic modulo;
- pop physically removes its front slot, and a drained queue resets `head` to zero.

`hasOffset` distinguishes a present zero value from absence. `getD` deliberately keeps the raw
storage fallback contract for missing or malformed values. Metadata is authoritative in this
slice: the fixture's mutating `pop` removes the addressed slot and returns the remaining length;
consumers use `peek`/`getAt` when they need the value. A future richer state/entry ABI may combine
the evicted value with metadata without weakening the bounded layout.

Prefixes remain caller-owned namespaces and must stay disjoint from all map, set, vector, queue,
raw, and compiler state-field keys. Generic values, resizing, iteration, hidden flushes, and
persistent collection metadata are outside this slice.

## Verification

- `Tests.NearQueueSpec` pins capacity and metadata laws, one-wrap physical indexes, exact key
  bytes, read/has/write/remove extraction, WAT arithmetic/imports, and canonical digest.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearQueue` fixture.
- `runtime-tests/near/queue.sh` deploys to near-sandbox 2.13.0 and verifies canonical empty state,
  exact `QUE1 || u32_le(slot)` keys and Borsh values, zero-value presence, FIFO order, capacity and
  large-offset rollback, tail/head wraparound, per-pop key reclamation, drained reset, and
  malformed-metadata fail-closed behavior.

## Next

Specify bounded direct IterableMap/IterableSet composition. It must pin key-vector and lookup
namespaces, swap-remove/index-record behavior, immediate persistence, and partial-failure rollback
without claiming near-sdk-rs cache/Drop timing.
