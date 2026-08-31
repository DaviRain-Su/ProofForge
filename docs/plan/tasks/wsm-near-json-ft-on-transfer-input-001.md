---
id: wsm-near-json-ft-on-transfer-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-message-input-001, wsm-near-json-u128-input-001]
---

# wsm-near-json-ft-on-transfer-input-001 bounded receiver arguments

## Objective

Decode the receiver callback object `{sender_id,amount,msg}` into a complete AccountId, lossless
u128, and bounded UTF-8 message without exporting `ft_on_transfer` or defining receiver behavior.

## Delivered

- Compiler-owned `FtOnTransferArgs` has exactly sender AccountId9, amount2, and Message64 nine
  leaves. Ordinary same-shaped records and incomplete/extended lookalikes do not bind.
- `near-json-ft-on-transfer-args-bounded-v1(max-wire=1071,ws=32,order=any,keys=raw,unknown=reject)`
  accepts all six known-field permutations. The three required fields use independent presence
  bits; message accepts empty but missing/null, duplicate, unknown/escaped keys, wrong types,
  trailing input, malformed Unicode/UTF-8, and capacity overflow reject.
- The exact maximum is 37 structural bytes plus worst-case six-byte escapes for a 64-byte sender,
  39 amount digits, and 64 decoded message bytes, plus 32 aggregate structural whitespace bytes.
  Existing AccountId syntax, checked u128 decimal, and shared Unicode string decoders are reused.
- IR/WAT checks pin the exact schema, 20 locals, policy/digest, one loop parser, one bounded host
  input read, and a pre-zeroed 160-byte frame. near-sandbox covers six orders, raw/escaped and
  supplementary Unicode, empty/max frames, malformed and over-bound matrices, inactive zeros,
  stale isolation, mutating use, and rollback after a parse failure.

## Boundary

This is a bounded canonical subset, not generated near-sdk serde compatibility: keys must have raw
exact spelling, unknown fields reject, and whitespace/wire size are capped. It adds no standard
`ft_on_transfer` export, receiver acceptance/refund policy, ledger write, event, or Promise effect.
