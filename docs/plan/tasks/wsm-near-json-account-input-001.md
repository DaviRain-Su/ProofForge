---
id: wsm-near-json-account-input-001
scope: wasm
status: done
depends-on: [wsm-near-memory-001, wsm-020]
---

# wsm-near-json-account-input-001 bounded AccountId JSON object view input

## Objective

Add the smallest AccountId JSON-input prerequisite for later NEP views: decode one exact
compiler-owned AccountId parameter from an official-shaped `{"account_id":"..."}` object without
opening a generic JSON ABI or implementing an FT method.

## Delivered

- Exact schema matching binds only `ProofForge.Wasm.Near.Runtime.AccountId` with ordered
  `length,w0..w7` UInt64 leaves. Ordinary same-shaped records, mutating methods, and multiple
  parameters fail closed. The canonical bounded policy participates in the target digest.
- The host register is bounded to 433 bytes before one read into checked arena memory. That bound
  is exact geometry for 17 structural bytes, 64 bytes each encoded as `\uXXXX`, and a separate
  aggregate allowance of 32 JSON whitespace bytes. A zeroed 64-byte decoded frame produces the
  exact active length and eight little-endian words; inactive bytes stay zero.
- Accepted grammar is deliberately narrower than near-sdk-rs's serde-generated wrapper: exactly
  one raw-spelled `"account_id"` key; SP/TAB/CR/LF at structural boundaries; standard value
  escapes and upper/lower Unicode hex when the decoded byte is ASCII; exact EOF. Unknown,
  duplicate, escaped-key, missing, wrong-type, trailing, malformed escape, non-ASCII, surrogate,
  and over-budget inputs reject.
- Decoded identity is 2..64 bytes of lowercase ASCII letters, digits, `-`, `_`, or `.`, with no
  leading, trailing, or adjacent separators. This parser establishes the nominal syntax needed by
  later specialized views.
- Targeted extraction/WAT gates pin one input read, checked allocations, parser/helper inclusion,
  schema discrimination, view-only rejection, carrier loading, and digest. A near-sandbox suite
  covers raw/escaped minimum and maximum identities, asymmetric limbs, inactive zeroing, exact
  wire/whitespace boundaries, and the malformed object/string/account matrix.

## Boundary

near-sdk-rs generated wrappers use serde_json and therefore accept a broader grammar (including
escaped field names and, by default, ignored unknown fields). This ProofForge policy intentionally
rejects those forms and is named as a bounded subset. It is not generic JSON, not a public NEP-141
method ABI, and does not yet compose the existing balance map or quoted-u128 output into
`ft_balance_of`.
