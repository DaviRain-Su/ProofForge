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
- NEAR example: `Examples.NearTokenErgonomics.addViaAndThen`
- EVM example: `Examples.EvmExceptErgonomics.addViaAndThen` (digest `8def48aa72cd2c19`)

## Follow-up

- Optional `do` notation guide in docs
- SVM `andThen` cookbook example
- Structure-valued `Except.ok` Decode (blocked for `NearToken.addChecked`)
