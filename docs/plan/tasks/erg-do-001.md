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

## Follow-up

- Extract support for `andThen` on NEAR/SVM/EVM targets (currently use explicit `match` in on-chain examples)
- Optional `do` notation guide in docs once extraction lands
