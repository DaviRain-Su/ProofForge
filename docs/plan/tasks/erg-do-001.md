---
id: erg-do-001
scope: shared
status: partial
depends-on: []
---

# erg-do-001 — Core.Except combinators

## Delivered

- `ProofForge.Core.Except`: `ok`, `err`, `andThen`, `map`, `guard`
- Imported through root `ProofForge` module
- Extract: `Core.Except.andThen` sequenced like `Bind.bind`; `ok`/`err` recognized alongside std `Except`
- NEAR example: `Examples.NearTokenErgonomics.addViaAndThen` + **`addCheckedViaAndThen` / `addCheckedHelperViaAndThen` / `addCheckedDirect`** (JSON u128 `NearToken` mutating return; digest `c2e097e411bbd3b4`)
- EVM example: `Examples.EvmExceptErgonomics.addViaAndThen` (digest `8def48aa72cd2c19`)
- SVM example: `Examples.SvmExceptErgonomics.addViaAndThen` (extract digest `d826699c521e0b7c`)

## Follow-up

- ~~Optional `do` notation guide in docs~~ — **done** (`docs/plan/do-notation-guide.md`)
- Extract `PromiseHandle`-typed entry bodies for NEAR N13
