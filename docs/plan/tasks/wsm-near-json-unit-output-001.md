---
id: wsm-near-json-unit-output-001
scope: wasm
status: done
depends-on: [wsm-near-output-001]
---

# wsm-near-json-unit-output-001 mutating Unit output

## Objective

Return exact JSON `null` from a successful NEAR mutation whose explicit logical result is `Unit`,
without changing historical raw-UInt64 mutations or introducing generic JSON serialization.

## Delivered

- The extractor retains explicit `Except Error (State × Unit)` as a zero-leaf `.unit` result. Its
  historical scalar success terminal uses a control-only zero carrier; NEAR's schema-owned output
  path never publishes or stores that carrier.
- Only a mutating Unit result selects `near-json-null-unit-v1`. Initializers remain unchanged and a
  Unit view rejects rather than silently choosing this mutation policy.
- The emitter stages exact UTF-8 `null` in a four-byte arena allocation and performs one final
  `value_return`. State stores happen first; a failed source branch traps and nearcore rolls them
  back. Promise-return and JSON-null return cannot be combined.
- Targeted extraction/IR/WAT checks pin zero leaves, policy, mutating classification, endian
  constant, one four-byte return, malformed-frame rejection, and unchanged raw UInt64 output.
  The near-sandbox gate proves exact SuccessValue bytes, persisted state, repeated invocations, and
  failed-call rollback.

## Authoritative boundary

Current near-sdk-rs macros distinguish an omitted Rust return annotation from explicit `-> ()`.
The explicit form is a general result, uses the default JSON serializer, and calls
`env::value_return`; `serde_json::to_vec(&())` is exactly `null`. The omitted form emits no return.
ProofForge implements only the explicit logical Unit case and does not add a generic serializer.

## Next

Compose this output with the bounded `FtTransferArgs` input, one-yocto guard, existing `BAL2`
ledger, and exact NEP-141 event in a separate `ft_transfer` slice.
