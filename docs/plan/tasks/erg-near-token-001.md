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
- Example `Examples.NearTokenErgonomics` + **`addViaAndThen`** (`Core.Except.andThen` Extract) + registry digest `cfc8d03d4e1883a5`

## Follow-up

- Wire `NearToken.addChecked` through Extract for NEAR mutating entries
- Refactor `NearFungibleLedger.ft_transfer` to use `addChecked` once extraction supports it
