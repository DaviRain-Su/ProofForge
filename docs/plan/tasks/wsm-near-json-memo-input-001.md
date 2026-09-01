---
id: wsm-near-json-memo-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-account-input-001, wsm-near-json-u128-input-001]
---

# wsm-near-json-memo-input-001 optional bounded memo JSON input

## Objective

Add the optional UTF-8 memo parser prerequisite for a later specialized `ft_transfer` object,
without adding that method or a generic JSON ABI.

## Delivered

- Compiler-owned `OptionalMemo16` distinguishes `None` from `Some ""` with exact
  `(present,length,w0,w1)` leaves. Active UTF-8 bytes are packed little-endian and inactive bytes
  are zero. Ordinary same-shaped records and ordinary `Option` values do not bind this policy;
  view and mutating wrappers can both reuse it.
- Canonical objects accept `{}` and `{"memo":null}` as `None`, or one raw-spelled memo field with a
  string as `Some`. Unknown, duplicate, escaped-key, wrong-type, and trailing forms reject.
  Structural SP/TAB/LF/CR is limited to 32 bytes independently of spaces inside the memo.
- The reusable string component decodes all JSON short escapes, BMP `\uXXXX`, and valid high/low
  surrogate pairs into canonical UTF-8. Raw valid UTF-8 is preserved. Malformed UTF-8, raw
  controls, invalid hex, isolated/reversed surrogates, and unknown escapes reject.
- Decoded capacity is exactly 16 UTF-8 bytes. The 139-byte wire limit is exact for 11 structural
  bytes, sixteen six-byte escapes, and 32 structural whitespace bytes. Targeted WAT and real
  near-sandbox scenes pin None/Some-empty, controls/NUL/quote/backslash, non-ASCII/emoji, exact
  capacity and wire limits, inactive zeroing, mutating use, and malformed matrices.

## Boundary

near-sdk-rs derives ordinary serde `Option<String>` arguments: missing and explicit null are
`None`, empty string is `Some("")`, and there is no SDK memo length bound. ProofForge deliberately
adds a 16-decoded-byte compiler resource bound and rejects unknown fields, so this is a named
canonical subset, not serde compatibility or a public FT method.
