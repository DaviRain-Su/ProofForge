---
id: wsm-near-json-storage-deposit-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-account-input-001, wsm-near-storage-balance-bounds-001]
---

# wsm-near-json-storage-deposit-input-001 bounded storage-deposit arguments

## Objective

Add the exact compiler-owned input carrier needed by a later closed `storage_deposit` integration,
without exporting the standard method or claiming generic serde compatibility.

## Delivered

- `StorageDepositArgs` is an exact eleven-leaf frame: account presence, the existing nine-leaf
  AccountId, and a `None`/`Some false`/`Some true` registration-only discriminant.
- One field loop accepts `{}`, missing/null option fields, both known fields in either order,
  decoded AccountId escapes, and booleans. It rejects duplicate, unknown, escaped keys, wrong
  types, trailing tokens/commas, invalid AccountIds, more than 32 structural whitespace bytes,
  and wire input above 459 bytes.
- The exact maximum is `43 + 64×6 + 32 = 459`: the two-field `false` form, a maximally escaped
  64-byte AccountId, and the aggregate whitespace allowance. Inactive AccountId leaves are zero.
- View and mutating diagnostic methods prove exact leaves, stale isolation, state persistence, and
  rollback on a late parse failure in real nearcore. No diagnostic uses the standard export name.

## Boundary

near-sdk's generated wrapper maps missing/null fields to `None`, rejects duplicate known fields,
but accepts unknown fields unless `deny_unknown_arguments` is requested. ProofForge deliberately
uses a bounded canonical subset with raw known keys and unknown rejection, so this is not full
near-sdk serde compatibility. The later operation must default a missing account to predecessor;
the vanilla FT ignores `registration_only` behaviorally and refunds deposits asynchronously.
