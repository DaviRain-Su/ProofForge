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
2. `Examples.EvmTokenErgonomics` — sequential `approve` / `transfer` / `transferFrom` (digest `138c08a82e1ad205`)
3. `Tests.EvmTokenErgonomicsSpec` + registry pin; EVM artifact count → 46
4. Full `Examples.Token` migration deferred (kernel supply proofs are nested-`if`-shaped)

## Landed (Token Bool ABI trio)

5. `Examples.Evm.Token.approve` / `transfer` / `transferFrom` use `Effect.ensure` / `hold`;
   supply-preservation theorems retargeted; registry digest `f6a3fcbc3c7331fe`
   (was `b69773a11a64286e` → `1dc6b7a9d09f1478` after approve-only)

## Follow-up

- Port mint/burn/allowance/pause gates to `Effect.ensure` where CallResult-shaped
- Nested-`if` remains on UInt64-returning mutators for now

## Non-goals

- CallResult interpreter / R5-012 policy change
- `erg-svm-account-001` cookbook
- Implicit state (`erg-state-001`)

## Acceptance (slice)

§5.3 “Token mint/transfer like sequential statements” holds on `EvmTokenErgonomics`; digest pinned.
Token `approve` is sequential; `transfer` / `transferFrom` remain nested-`if`.
