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

## Follow-up

- Optional `do` notation guide in docs
- SVM/EVM examples using `andThen` chains (NEAR `addViaAndThen` landed)
