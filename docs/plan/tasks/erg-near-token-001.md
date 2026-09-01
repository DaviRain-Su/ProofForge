---
id: erg-near-token-001
scope: wasm
status: done
depends-on: []
---

# erg-near-token-001 — NearToken high-level SDK surface

## Delivered

- `NearToken.isZero`, `le`, `lt`, `ofLimbs`
- Checked helpers: `add?`, `sub?`, `mulUInt64?`, `addChecked`, `subChecked`, `mulUInt64Checked` (source/proof layer; NEAR Extract for `addChecked`/`andThen` chains remains follow-up)
- Legacy limb API (`addW0`, `canAdd`, …) preserved
- Example `Examples.NearTokenErgonomics` + **`addViaAndThen` / `addCheckedViaAndThen`** (`Core.Except.andThen` + JSON u128 `NearToken` return) + registry digest `ab9da3168e8cd786`

## Follow-up

- Wire inline `NearToken.addChecked` through Extract for NEAR mutating entries (2026-09-01: explicit `if canAdd / ofLimbs` works; inline helper still differs)
- Refactor `NearFungibleLedger.ft_transfer` to use `addChecked` once extraction supports it
