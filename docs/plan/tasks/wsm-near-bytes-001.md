---
id: wsm-near-bytes-001
scope: wasm
status: done
depends-on: [wsm-near-log-001, r1-015]
---

# wsm-near-bytes-001 NEAR canonical Borsh bounded bytes/string input

## Objective

Bind shared allocation-free `BoundedBytes` / `BoundedString` source carriers to one canonical
NEAR Borsh input frame before opening binary storage or collections. Keep collections as future
SDK compositions over storage; do not invent Vector/Map VM imports or source-visible pointers.

## Delivered

- `Near.Codec.BorshInputPlan` accepts exactly one top-level bounded bytes or string parameter with
  capacity 1..64. Its canonical policy participates in the target IR digest.
- NEAR target binding rewrites the logical `length + fixed byte slots` carrier to UInt64 locals,
  shifts the managed State argument, and rewrites literal or runtime byte projections without
  adding per-byte Runtime leaves.
- The entry decoder reads `env.input` through one bounded register span at memory offset 256,
  requires exact `u32_le(length) || active bytes`, rejects short/trailing/over-capacity payloads,
  and explicitly zeroes every inactive local before source execution.
- `BoundedString` uses a generated strict Unicode-scalar UTF-8 validator. It rejects overlong
  encodings, surrogates, truncation, stray continuations, and values above U+10FFFF;
  `BoundedBytes` preserves the same byte sequences.
- Existing raw-u64 Counter/NearCtx and XRPL digests remain unchanged. Bounded output is not
  enabled: views still publish one raw 8-byte little-endian UInt64.

## Verification

- `Tests.NearBytesSpec` pins logical schemas, nine-local frames, policies, rewritten operations,
  memory bounds, exact-length checks, inactive zeroing, and UTF-8 helper anchors.
- The pinned `wat2wasm 1.0.41` engineering gate assembles all three registered NEAR programs.
- near-sandbox 2.13.0 accepts byte lengths 0/1/8 and valid ASCII/2/3/4-byte UTF-8; it rejects
  short, mismatched, trailing, over-capacity, overlong, surrogate, truncated, stray-continuation,
  and out-of-range inputs. Malformed UTF-8 remains accepted by the bytes entry.

## Next

The invocation-local guest arena landed independently in wsm-near-memory-001 before output/storage
work. Next add a bounded Borsh output/static-aggregate plan without reusing input geometry, then
implement arbitrary binary storage read/write/remove/exists with explicit host status and bounded
register results. Only after that storage contract is verified should `store::Vector`, LookupMap,
LookupSet, or a separately specified bounded Queue receive a NEAR SDK binding.
