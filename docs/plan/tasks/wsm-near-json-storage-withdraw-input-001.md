---
id: wsm-near-json-storage-withdraw-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-input-001, wsm-near-json-storage-unregister-input-001]
---

# wsm-near-json-storage-withdraw-input-001 bounded optional amount input

## Objective

Add the exact compiler-owned optional quoted-u128 argument frame needed by a later public-shaped
`storage_withdraw`, without exporting that method or adding storage/refund behavior.

## Delivered

- `StorageWithdrawArgs` is an exact three-leaf frame: one presence discriminant and two full-width
  amount limbs. Missing `{}` and explicit `null` produce None with both inactive limbs zero;
  canonical quoted decimals produce Some and preserve low/high limb order.
- The raw `amount` key object parser reuses the checked decimal string decoder. It accepts 1..39
  decoded digits including digit-producing Unicode escapes and rejects leading zeroes, signs,
  overflow, duplicate/unknown/escaped keys, wrong types, malformed UTF-8, and trailing input.
- The exact 279-byte maximum is 13 structural bytes plus 39 worst-case six-byte escapes and 32
  structural whitespace bytes. One host input/register read and a freshly zeroed 24-byte frame
  prevent stale inactive data.
- The diagnostic fixture supports view and mutating wrappers but deliberately has no
  `storage_withdraw` export, ledger effect, native refund, or NEP-145 compatibility claim.

## Boundary

The accepted grammar is a bounded canonical subset. Current near-sdk serde accepts a broader JSON
language, while ProofForge rejects unknown fields, escaped key spelling, and excess whitespace.
