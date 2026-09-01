---
id: wsm-near-json-u128-mutation-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-output-001, wsm-near-state-envelope-001]
---

# wsm-near-json-u128-mutation-output-001 mutating quoted-u128 output

## Objective

Return an exact canonical quoted-decimal full-u128 value from a successful state mutation without
aliasing the result limbs with terminal state destinations or changing any other return policy.

## Delivered

- The extractor retains both ordered UInt128 constructor leaves for the exact
  `Except Error (State × UInt128)` source shape. NEAR lowering selects the existing
  `near-json-u128-string-v1` policy only for that exact scalar mutation; ordinary two-field records,
  explicit Unit, omitted returns, and malformed frames do not bind.
- The emitter writes every state field before staging one 3..41-byte quoted decimal and issuing
  exactly one `value_return`. Promise-return composition rejects. Source errors trap, so nearcore
  rolls back any executing-receipt writes.
- The targeted fixture pins two independent state fields and asymmetric result limbs `(2,1)` in
  extraction, IR policy/digest, and WAT ordering. Its near-sandbox scene proves the exact
  `"18446744073709551618"` bytes, persisted fields, repeated-call destination isolation, and failed
  mutation rollback. Existing view u128, raw UInt64, JSON-null Unit, void-empty, and Promise output
  regressions remain unchanged.

## Boundary

This is one compiler-owned mutation result shape, not generic JSON serialization or a public ABI.
It exists for the later private FT resolver, whose state reconciliation and argument parser remain
separate slices.
