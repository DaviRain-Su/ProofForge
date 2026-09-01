---
id: wsm-near-nep141-event-003
scope: wasm
status: done
depends-on: [wsm-near-nep141-event-002, wsm-near-bytes-001]
---

# wsm-near-nep141-event-003 bounded memo event variants

## Objective

Add the official optional memo field to each closed NEP-141 v1.0.0 fungible-token event without
changing the existing no-memo bytes or introducing token state, method ABI, or generic JSON.

## Delivered

- `mintWithMemo`, `transferWithMemo`, and `burnWithMemo` accept an explicit bounded UTF-8 memo and
  lower through dedicated Runtime effects and complete Extract/Ops/IR/CFG/canonical payloads.
- Records retain near-sdk-rs declaration order: owner field(s), quoted full-u128 `amount`, then
  `memo`. Empty memo remains present as `"memo":""`; no-memo APIs still omit the field.
- Dynamic memo bytes reuse the serde_json-compatible escaper: quote/backslash and short controls
  are escaped, other controls use lowercase `\u00xx`, and valid non-ASCII UTF-8 is preserved.
- Exact checked arena geometry is 634 bytes for 16-byte mint/burn memos and 1,044 bytes for
  transfer. A specialized 16-byte compiler bound keeps the statically selected scalar frame below
  nearcore's per-function control-flow limit; the well-formedness predicate also pins single-event
  geometry below the 16,384-byte cumulative host log budget. Each event performs one final
  `env.log_utf8`.

## Verification

- Lean guards pin 17-leaf bounded frames, amount limbs, owner frames, canonical digest, allocation
  constants, helper/export anchors, and the accepted 16-byte capacity boundary.
- near-sandbox compares exact compact logs for empty, quote/backslash/control, non-ASCII, and full
  16-byte memos while rerunning every no-memo event byte-for-byte.

## Not included

- Balances, total supply, FT methods, storage management, resolver callbacks, arbitrary event
  arrays, generic JSON ABI, or a complete NEP-141 fungible-token contract.
