---
id: wsm-near-json-storage-unregister-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-storage-deposit-input-001]
---

# wsm-near-json-storage-unregister-input-001 bounded unregister arguments

## Objective

Add the exact compiler-owned input carrier needed by a later `storage_unregister` integration,
without exporting the standard method or performing lifecycle effects.

## Delivered

- `StorageUnregisterArgs` is one scalar leaf. Its `force` value is `0`, `1`, or `2` for a missing
  or null option, `Some false`, or `Some true`.
- The parser accepts `{}`, `{"force":null}`, `{"force":false}`, and `{"force":true}` with at
  most 32 structural whitespace bytes. It rejects duplicate, unknown, or escaped keys, wrong
  types, malformed literals, trailing tokens/commas, and input above 47 bytes.
- The exact maximum is `15 + 32 = 47`: compact `{"force":false}` plus the aggregate whitespace
  allowance. View and mutating diagnostics prove the discriminant, state persistence, stale
  isolation, and rollback after a late parse failure in real nearcore.
- The exact compiler-owned schema binds the policy into target IR and its digest; an ordinary
  one-field record is not recognized. The fixture does not export `storage_unregister`.

## Boundary

Current near-sdk maps missing/null `Option<bool>` to `None` and rejects duplicate known fields,
but stock serde accepts unknown fields. ProofForge deliberately uses a bounded canonical subset
with raw known keys and unknown rejection, so this parser is not full near-sdk serde compatibility.
The later integration remains responsible for exact-one-yocto, registration, supply, reclaim,
refund, and JSON Boolean-return semantics.
