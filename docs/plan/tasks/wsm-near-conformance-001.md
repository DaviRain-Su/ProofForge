---
id: wsm-near-conformance-001
scope: near
status: partial
depends-on: [wsm-near-ft-ledger-001]
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# wsm-near-conformance-001 — Counter/Token cross-target conformance (N15)

## Goal

Document and pin **shared semantic fixtures** that build on SVM, EVM, and NEAR from the
same Lean source, without pretending wire formats or storage geometry are identical.

## Landed (Counter first slice)

1. `Tests/CrossTargetCounterSpec` — authoritative three-target digest table for
   `Examples.Counter`:
   | Target | Registry digest |
   |---|---|
   | SVM | `3382e308fa0843e9` |
   | EVM | `254202356ee921d6` |
   | NEAR | `121a0c8f7e697642` |
2. Verifies shared entry surface (`initialize`, `increment`, `get`, …) across lowers
3. Reuses `#pf_near_build` / `#pf_evm_build` registry checks

## Follow-up

- Token-shaped cross-target table (`Examples.Token` / `NearFungibleLedger` / SVM token fixtures)
- Runtime sandbox matrix pointers in one doc (near `ledger.py`, Anvil, Mollusk)
- Optional CI lane label `conformance` (currently covered by aggregate Lean gate)

## Non-goals

- Shared wire encoder or unified ABI
- XRPL (explicitly out of multi-target scope)

## Acceptance

N15 Counter row → **partial** (digest table + method surface pinned); Token table follow-up.
