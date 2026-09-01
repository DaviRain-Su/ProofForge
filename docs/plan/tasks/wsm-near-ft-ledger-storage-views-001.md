---
id: wsm-near-ft-ledger-storage-views-001
scope: wasm
status: done
depends-on: [wsm-near-ft-ledger-metadata-001, wsm-near-storage-balance-of-001, wsm-near-storage-balance-bounds-001]
---

# wsm-near-ft-ledger-storage-views-001 integrated storage views

## Objective

Compose the verified variable-cost NEP-145-shaped registration queries with the same `BAL2`
artifact that owns fungible balances, supply, transfer, resolver, and metadata behavior.

## Delivered

- `NearFungibleLedger` exports exact `storage_balance_of` and `storage_balance_bounds` beside its
  NEP-141/148-shaped methods; both inspect the canonical balance/registration namespace directly.
- Present exact-16 balances report `(active AccountId bytes + 64) × 1 yoctoNEAR` total and zero
  available. Missing accounts return `null`; malformed values fail closed. Bounds report the true
  accepted 2..64-byte extrema, 66 and 128, and ignore request bytes.
- Structural and real-nearcore tests pin exact specialized input/output policies, no mutation,
  logs, or Promise effects, short/max active-byte geometry, malformed rejection, and unchanged
  existing ledger behavior.

## Compatibility boundary

The one-yocto-per-byte price is an explicit immutable fixture profile, not a guessed network price.
The AccountId input is ProofForge's bounded canonical subset and the variable bounds differ from
near-contract-standards' fixed maximum-account storage charge. This slice therefore proves artifact
composition without claiming complete NEP-145 ABI or economics compatibility.
