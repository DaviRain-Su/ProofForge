# wsm-near-output-001 — NEAR allocator-backed bounded Borsh output

Status: done

## Scope

NEAR view methods can now return canonical Borsh bounded bytes, bounded strings, and bounded arrays
of one-limb unsigned UInt8/16/32/64 elements. Extract retains the logical output schema and fixed
source frame `length, slot₀ … slotₙ₋₁`; `Near.IR` binds an independent output plan, and `Near.Emit`
serializes only `u32_le(length) || active elements` into the wsm-near-memory-001 guest arena before
calling `value_return`.

The output capacity is compiler-bounded to 1..64. Runtime length must not exceed capacity. Narrow
lanes are checked before storing so malformed fixed frames cannot be silently truncated. String
output runs the same Unicode-scalar strict UTF-8 validator as String input. Arena pointers remain
target-private, and only the initialized active prefix is published. Mutating bounded results,
nested aggregates, tagged values, and JSON remain fail closed.

## Verification

- `Tests.NearOutputSpec` pins plan geometry, logical metadata, fixed return counts, canonical digest,
  policy consistency, view-only restrictions, narrow stores, bounds, UTF-8, and arena/value_return
  WAT anchors.
- Pinned `wat2wasm 1.0.41` assembles `NearOutput.wasm`.
- `runtime-tests/near/output.sh` deploys to near-sandbox 2.13.0 and checks exact empty/bytes/String/
  UInt16-array output, bounded input/output round trips, malformed output UTF-8, and capacity traps.
- Existing scalar NEAR and XRPL digests remain unchanged.

## Next

Bounded raw binary storage with explicit host status semantics and allocator-backed register copies
landed in [wsm-near-storage-001](wsm-near-storage-001.md). Durable current-layout Vector is next,
followed by LookupMap/Set and an explicitly specified bounded Queue; the arena remains scratch,
never persistence.
