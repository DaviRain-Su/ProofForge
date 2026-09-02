---
id: wsm-near-promise-general-001
scope: wasm-near
status: partial
depends-on: []
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# wsm-near-promise-general-001 — bounded Promise handle generalization (N13)

## Context

N12 public FT surface is on main (`Examples.NearFungibleLedger` + sandbox). Existing Promise
tasks cover static call / return / two-child join. Generalization is blocked until a
source-visible handle + lifecycle contract exists (`wsm-near-promise-and-001` note).

## Design sketch (greenfield, Feature A only)

### Source handle

```text
structure PromiseHandle (maxFanIn : Nat) where
  id     : UInt64          -- host promise index; opaque to apps
  depth  : UInt8           -- creation depth; join increments
  fanIn  : Fin (maxFanIn+1)
```

- `maxFanIn` is a compile-time capacity (suggested default **4**; hard ceiling **8**).
- Handles are **not** copyable across unrelated entries without an explicit rebind effect.
- Extract rejects any Promise API whose `maxFanIn` literal exceeds the profile ceiling.

### Lifecycle ops (SDK-shaped)

| Op | Meaning | Fail-closed edge |
|---|---|---|
| `Promise.create` | new root handle (`depth=0`, `fanIn=0`) | gas/deposit policy stays target-owned |
| `Promise.then` | attach one callback; returns same handle family | depth ≥ ceiling |
| `Promise.and` | N-way join of `2..maxFanIn` handles | fan-in overflow; mismatched batch |
| `Promise.transfer` | NEAR transfer leaf | amount/account validation |

N-way `and` is a single Extract-visible op with a **fixed** argument vector of length
`maxFanIn` plus a runtime `used : Fin (maxFanIn+1)` count (inactive slots zero / unused).

### Concurrency model

- Keep today's static DAG spelling: no open-world promise maps.
- Joins remain **batch-shaped** (array of handles), not recursively nested `and(and(...))`
  beyond the depth ceiling — Encode depth in the handle so Extract can reject.
- Self-callback + join fixtures reuse near-sandbox patterns from N12 ledger tests.

### Implementation order

1. ~~`PromiseHandle` + create/then with depth gate~~ — **landed** in
   `ProofForge/Wasm/Near/Sdk/Promise.lean` (`createReturned`, `thenReturned`, `depthOk`);
   compile-time smoke in `Examples/NearPromiseHandle.handleDepthSmoke`; **`sendHandleThen` /
   `sendHandleAnd3` now use `promiseRoot.thenReturned` / `and3Returned`** (Extract decode landed)
2. ~~Fixed-capacity `andN` (N=3 first; generalize to maxFanIn)~~ — **landed** for N=3..**8**:
   `And3ThenReturned` / `And4ThenReturned` / `And5ThenReturned` / `And6ThenReturned` /
   **`And7ThenReturned`** / **`And8ThenReturned`**,
   matching SDK/Extract/Emit/fixtures through **`sendAnd8*`** / **`callbackJoined8`**;
   registry digest updates with each N;
   **`maxFanInCompileCeiling := 8`** + `maxFanInWithinCeiling` / `withinCompileCeiling` smoke
   (`Examples.NearPromiseHandle.handleFanInSmoke`); **no And9** — hard ceiling stays 8
3. ~~Sandbox DAG: create→then; create×3→and→callback~~ — **landed** in
   `runtime-tests/near/promise.py` (`sendAnd3Success` / `sendAnd3RightMissing` scenes on
   `NearPromise.wasm`); handle fixtures through `sendHandleAnd8` + registry digest `c5a967669da142d8`
4. ~~Docs + capability-matrix row~~ — **landed** (`capability-matrix.md` §5 NEAR Promise row;
   `multi-target-strategy.md` N13 status)
5. ~~Extract fail-closed N>8~~ — **landed** (`Decode.findPromiseHandleMaxFanInCeilingError`;
   `Tests.NearPromiseHandleSpec.OverCeilingFanIn` proves `maxFanIn=9` rejected)

## Still open

- Generic compile-time parameterized `andN` (would still need new ops to raise the ceiling)
- ~~Extract of handle-typed entry bodies~~ — **landed** (`PromiseHandle.thenReturned` /
  `and3Returned`..`and8Returned` + Extract capacity-offset decode; `sendHandleThen` /
  `sendHandleAnd3`..`sendHandleAnd8` gates in `Tests/NearPromiseHandleSpec`)
- ~~Extract reject for `maxFanIn` above ceiling~~ — **landed** (ceiling remains **8**)

## Deliverables

1. Source-level bounded Promise handle type (fail-closed max fan-in / depth)
2. N-way join within the bound; reject over-bound statically or at Extract
3. near-sandbox DAG fixtures for join + self-callback
4. No XRPL work

## Non-goals

Unbounded Promise graphs; host-side nondeterminism modeling; XRPL.

## Acceptance

N13 row in `multi-target-strategy.md` → done with sandbox evidence.
