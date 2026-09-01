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
- NEAR example: `Examples.NearTokenErgonomics.addViaAndThen` + **`addCheckedViaAndThen`** / **`addCheckedDirect`** (JSON u128 `NearToken` mutating return; digest `ab9da3168e8cd786`)
- EVM example: `Examples.EvmExceptErgonomics.addViaAndThen` (digest `8def48aa72cd2c19`)
- SVM example: `Examples.SvmExceptErgonomics.addViaAndThen` (extract digest `d826699c521e0b7c`)

## Follow-up

- Optional `do` notation guide in docs
- Structure-valued `Except.ok` Decode for inline `NearToken.addChecked` — **done** via `ofLimbs (addW0 …) (addW1 …)` SDK spelling + producer unfold in fixed-limb bind
- Extract `PromiseHandle`-typed entry bodies for NEAR N13
