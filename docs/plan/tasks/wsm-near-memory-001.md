# wsm-near-memory-001 — NEAR invocation-local guest arena

Status: done

## Scope

nearcore exposes Wasm linear memory and `memory.grow`; it does not expose malloc/free host
functions. Current near-sdk-rs likewise installs a guest allocator (`wee_alloc` by default) and
uses it for invocation-local `Vec`, `String`, codec, promise, register, and store-cache buffers.
ProofForge therefore owns allocation in the generated guest module rather than inventing a NEAR
host import.

This slice adds a checked upward arena after static data and a narrow SDK consumer, `Buffer64`.
The capacity is compiler-erased metadata: source contracts never receive a raw linear-memory
pointer. Each arena-using export resets the cursor and active consumer state. Allocation uses
widened arithmetic, 8-byte alignment, `memory.size`, and metered `memory.grow`; invalid geometry,
memory32 overflow, failed growth, bounds violations, stale/wrong handles, and overlapping active
buffers trap. Beginning a buffer zeroes its active range so reused invocation-local memory cannot
leak stale values.

## Boundary

- `Near.Memory` owns the pure page/alignment/growth model and resource limits.
- `Near.Sdk.Transient` owns the compiler-erased `Buffer64` source API.
- `Near.Ops` / `Near.IR` own canonical begin/set/get/finish operations.
- `Near.Emit` owns static arena placement and Wasm helper lowering.
- The arena is not durable state and does not replace NEAR KV storage.
- Future Vector/Map/Queue implementations must persist durable elements in NEAR storage. They may
  use the arena only for invocation-local serialized keys/values, codec scratch, and caches.

## Verification

- `Tests.NearMemorySpec` checks the pure allocator model, extraction/effect order, canonical IR,
  registry digest, reset placement, growth, zeroing, and trap anchors.
- The pinned `wat2wasm 1.0.41` gate assembles `NearMemory.wasm`.
- `runtime-tests/near/memory.sh` deploys to pinned near-sandbox 2.13.0 and exercises round-trip,
  two allocations crossing the source-declared first page, reuse, zero-on-begin, bounds, stale
  handle, wrong capacity, and double begin. nearcore may normalize a larger initial memory, so the
  actual `memory.grow` branch is pinned by the pure model and assembled-WAT gate rather than claimed
  as a sandbox observation.

## Next

The arena-backed bounded Borsh view output landed in wsm-near-output-001. Next use the same
invocation-local substrate for raw binary storage register copies. Keep persistent collection
layout and lifecycle independent from arena addresses; after raw storage is verified, add
current-layout Vector, LookupMap/Set, and a separately specified bounded Queue.
