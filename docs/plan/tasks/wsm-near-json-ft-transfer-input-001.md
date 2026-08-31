---
id: wsm-near-json-ft-transfer-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-account-input-001, wsm-near-json-u128-input-001, wsm-near-json-memo-input-001]
---

# wsm-near-json-ft-transfer-input-001 combined transfer argument parser

## Objective

Combine the bounded AccountId, quoted-u128, and optional memo value decoders in one exact
transfer-shaped object parser, without implementing or exporting the public FT method.

## Delivered

- Compiler-owned `FtTransferArgs` has exactly fifteen scalar leaves: receiver length plus eight
  words, amount low/high words, and memo present/length/two words. Ordinary same-shaped records,
  missing leaves, and extra leaves do not select the policy. View and mutating wrappers both bind.
- One bounded field loop accepts required raw-spelled `receiver_id` and `amount`, plus optional raw
  `memo`, in every order. Presence bits reject duplicate known keys and enforce required fields;
  unknown and escaped keys, wrong types, trailing commas/tokens, and malformed values fail closed.
- Missing and null memo both produce a fully zero None frame; an empty string remains present with
  zero length. AccountId, decimal amount, and memo decoded capacities remain independently 64,
  39 digits/full u128, and 16 UTF-8 bytes.
- Exact maximum wire geometry is 786 bytes: 40 structural bytes, 64×6 receiver bytes, 39×6 amount
  digits, 16×6 memo bytes, and 32 aggregate structural whitespace bytes. One host input/register
  read feeds a cleared 120-byte frame before any scalar local is loaded.

## Compatibility boundary

near-sdk-rs generated JSON arguments require `receiver_id` and `amount`, treat missing or null
`Option<String>` memo as None, and deserialize object fields independent of order. ProofForge
matches those field semantics within bounded value grammars, but rejects unknown fields and
escaped key spellings and limits whitespace/wire/decoded memo size. It is therefore a named
canonical subset, not full serde compatibility or NEP-141 method compliance. The fixture exports
only non-standard diagnostics and performs no token transfer.
