---
id: wsm-near-storage-unregister-integration-001
scope: wasm
status: done
depends-on: [wsm-near-json-storage-unregister-input-001, wsm-near-json-boolean-mutation-output-001, wsm-near-storage-force-unregister-001]
---

# wsm-near-storage-unregister-integration-001 bounded storage unregister

## Objective

Compose the specialized optional-force JSON input and mutating JSON Boolean output into exact
export `storage_unregister` over the existing canonical `BAL2` registration/balance map, without
creating a second ledger or claiming a complete NEP-145 ABI.

## Delivered

- Exact attached one yocto is checked before storage effects. The immediate predecessor is always
  the lookup/removal target and dynamic refund recipient. Missing/null/false force values are
  equivalent; only true permits removing a positive balance.
- Missing emits exact ordinary log `The account <id> is not registered` and returns exact `false`
  without map or supply changes. Present zero and forced positive
  balances return exact `true`, remove the same exact-16 value, measure live reclaimed bytes, and
  refund `(caller.length + 64) × trustedPrice + 1`. Zero leaves supply unchanged; force subtracts
  both balance limbs from both supply limbs before removal. No NEP-141 event is emitted.
- Malformed values, positive non-force, supply underflow, cost multiplication overflow, and refund
  addition overflow fail closed. Failures after removal are synchronous receipt panics and real
  nearcore proves the map/state rollback. Asynchronous refund failure cannot roll back success.
- Structural tests pin the exact parser/output/payable policies, effect order, export spelling,
  predecessor deposit/read/missing-log/remove/refund path, state persistence before Boolean return,
  and one ordinary missing-path log.
  Sandbox scenes pin exact false/true bytes, predecessor refund including one yocto, zero/forced
  supply conservation, malformed/parser/deposit rejection, and post-remove rollback.

## Compatibility boundary

This operation intentionally differs from near-contract-standards 5.29 in several visible ways.
Its 47-byte bounded canonical input is narrower than generated serde, and all measured-economics
invariants fail closed. In particular, non-decreasing usage and cost multiplication overflow panic, while
`storage refund + 1` uses checked u128 addition rather than `saturating_add`. These stricter paths
roll back instead of returning a zero/saturated refund. Operation/output semantics otherwise
follow the standard, but these differences mean the exact export is not a claim of complete
NEP-145 ABI compatibility.
