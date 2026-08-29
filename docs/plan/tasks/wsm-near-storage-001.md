# wsm-near-storage-001 — NEAR bounded raw binary storage

Status: done

Depends on: [wsm-near-output-001](wsm-near-output-001.md)

## Scope

Add byte-exact, unprefixed `storage_read`, `storage_write`, `storage_remove`, and
`storage_has_key` to the NEAR Runtime and thin SDK. Keys and values use bounded source frames;
active bytes are staged in the wsm-near-memory-001 invocation arena before the nearcore host call.
Result capacity is compiler-bounded to 1..64 and never becomes a source-visible pointer.

The result API preserves nearcore semantics rather than collapsing them into a Boolean:

- read/remove status 0/1 means absent/present; write means inserted/replaced; has-key means
  absent/present;
- only status 1 for read/write/remove consults register 3, so a stale register after status 0 can
  never leak into the result;
- `register_len = u64::MAX` and host statuses outside 0/1 trap;
- `length` reports the actual value length. `fits = 0` means it exceeded the chosen capacity, no
  allocation or register copy occurred, and indexed byte reads return zero;
- empty keys and values are valid. A present empty value remains distinguishable from absence by
  status 1 with length 0;
- every storage operation replaces one invocation-local active result, which must be consumed
  before the next storage operation.

Raw keys are intentionally not silently prefixed or hashed. Compiler-generated ASCII state-field
keys are reserved, and callers/future collection instances own unique explicit binary prefixes.
The existing scalar-slot loader now checks that a colliding raw value is exactly 8 bytes before
copying it, turning malformed namespace collisions into a trap rather than a scratch overwrite.
Read/has-key remain view-safe; write/remove fail closed in views.

## Verification

- `Tests.NearStorageSpec` pins extraction, target projection, binary frame geometry, host/register
  sequencing, capacity checks, scalar-slot hardening, canonical digest, and view legality.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearStorage` fixture.
- `runtime-tests/near/storage.sh` deploys to near-sandbox 2.13.0 and checks binary and empty keys,
  insert/replace/eviction, same-invocation miss/stale-register isolation, present-empty values,
  oversized no-copy results, remove/second-remove, and has-key.
- The engineering gate pins all four storage imports and raw-storage result helpers/exports.

## Boundary and next

The current source API returns status, actual length, fit, and indexed bytes as scalar leaves. A
direct top-level bounded aggregate reconstructed after a storage effect is still rejected by the
extractor's effect-sequencing boundary; it must not be advertised as supported until that adapter
is implemented. The bounded direct-write Vector element-layout foundation landed in
[wsm-near-vector-001](wsm-near-vector-001.md); LookupMap/Set and an explicitly specified bounded
Queue follow. Arena bytes are scratch only, never persistent layout.
