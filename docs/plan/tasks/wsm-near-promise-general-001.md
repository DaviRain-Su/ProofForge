---
id: wsm-near-promise-general-001
scope: wasm-near
status: todo
depends-on: []
plan: ../multi-target-strategy.md
---

# wsm-near-promise-general-001 — bounded Promise handle generalization (N13)

## Context

N12 public FT surface is on main (`Examples.NearFungibleLedger` + sandbox). Existing Promise
tasks cover static call / return / two-child join. Generalization is blocked until a
source-visible handle + lifecycle contract exists (`wsm-near-promise-and-001` note).

## Deliverables

1. Source-level bounded Promise handle type (fail-closed max fan-in / depth)
2. N-way join within the bound; reject over-bound statically or at Extract
3. near-sandbox DAG fixtures for join + self-callback
4. No XRPL work

## Non-goals

Unbounded Promise graphs; host-side nondeterminism modeling.

## Acceptance

N13 row in `multi-target-strategy.md` → done with sandbox evidence.
