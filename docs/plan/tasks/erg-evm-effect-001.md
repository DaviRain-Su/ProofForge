---
id: erg-evm-effect-001
scope: ergonomics
status: partial
depends-on: [erg-do-001]
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# erg-evm-effect-001 — EVM Effect / CallResult sequential surface

## Goal

Without changing the R5-012 CallResult policy, make Token-shaped examples read as
**sequential fail-closed steps** (`Effect.ensure` / `Effect.abort` / `Effect.thenTrue`)
instead of nested `if`/`match`.

## Landed (first slice)

1. `ProofForge.Evm.Sdk.Effect.ensure` / `Effect.abort` — soft-abort keeps `.ok (state, Bool)`
2. `Examples.EvmTokenErgonomics` — sequential `approve` / `transfer` (digest `8e7ec772def9558a`)
3. `Tests.EvmTokenErgonomicsSpec` + registry pin; EVM artifact count → 46
4. Full `Examples.Token` migration deferred (kernel supply proofs are nested-`if`-shaped)

## Follow-up

- Port `Examples.Token` `approve`/`transfer`/`transferFrom` to `Effect.ensure` and regenerate
  supply-preservation proofs
- Update `docs/plan/do-notation-guide.md` once Token itself is sequential

## Non-goals

- CallResult interpreter / R5-012 policy change
- `erg-svm-account-001` cookbook
- Implicit state (`erg-state-001`)

## Acceptance (slice)

§5.3 “Token mint/transfer like sequential statements” holds on `EvmTokenErgonomics`; digest pinned.
