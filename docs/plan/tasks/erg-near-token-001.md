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

- Refactor `NearFungibleLedger.ft_transfer` / `ft_transfer_call` to use `NearToken.canSub`/`canAdd` + `ofLimbs` — **reverted for merge**: the helper form moved `nextSender` before the receiver `read` and broke present-zero retention under Extract (sandbox: `ft_transfer did not preserve registered present-zero source`). Restored main limb-capture order; digest `e1e290ddec221fa5`. Re-land only with an Extract-safe capture of sender limbs before any subsequent storage read.
- Wire `Except.andThen` + `subChecked`/`addChecked` in NEAR effectful increment methods once Extract supports `match`/`andThen` inside nested payable/void entry bodies
