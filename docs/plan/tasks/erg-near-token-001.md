---
id: erg-near-token-001
scope: wasm
status: done
depends-on: []
---

# erg-near-token-001 — NearToken high-level SDK surface

## Delivered

- `NearToken.isZero`, `le`, `lt`, `ofLimbs`
- Checked helpers: `add?`, `sub?`, `mulUInt64?`, `addChecked`, `subChecked`, `mulUInt64Checked` (source + NEAR Extract via `ofLimbs`/`addW0`/`addW1` path)
- Legacy limb API (`addW0`, `canAdd`, …) preserved
- Example `Examples.NearTokenErgonomics` + **`addViaAndThen` / `addCheckedViaAndThen` / `addCheckedHelperViaAndThen`** (`Core.Except.andThen` + JSON u128 `NearToken` return) + registry digest `c2e097e411bbd3b4`

## Follow-up

- Refactor `NearFungibleLedger.ft_transfer` to use `NearToken.addChecked` in `andThen` chains
