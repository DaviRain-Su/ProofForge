---
id: wsm-near-json-u128-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-output-001, wsm-near-json-account-input-001]
---

# wsm-near-json-u128-input-001 canonical quoted-u128 amount object input

## Objective

Add the reusable full-u128 decimal parser prerequisite for later FT method objects, without
opening a generic JSON ABI or claiming a public NEP method.

## Delivered

- Exact schema matching binds only one compiler-owned `.scalar .uint128` parameter to canonical
  policy `near-json-u128-amount-object-canonical-v1(max-wire=279,ws=32,digits=1..39,unknown=reject)`.
  Its two target locals are ordered `(w0,w1)`; ordinary two-field records and multiple parameters
  fail closed. Both view and mutating wrappers are supported for later FT composition.
- One bounded host input read stages at most 279 bytes: 13 structural bytes, up to 39 decoded
  digits represented by six-byte `\u00xx` escapes, and 32 aggregate structural whitespace bytes.
  A reusable in-memory quoted-decimal component checks overflow against max-u128 before exact
  two-limb multiply-by-10/add-digit accumulation.
- The accepted value is canonical decimal `0` or a nonzero digit sequence without leading zero.
  Digit-producing `\uXXXX` escapes are accepted. Raw/escaped plus, minus, nondigits, empty,
  overlong, max+1, malformed hex/surrogate, unknown/duplicate/missing/escaped keys, wrong types,
  trailing tokens, invalid UTF-8, and resource-bound violations reject.
- Targeted extraction/WAT gates pin exact schema discrimination, policy/digest, helper inclusion,
  one input/read pair, arena bounds, and low/high loads. near-sandbox covers 0, 2^64, 2^64+1,
  asymmetric limbs, max-u128, escaped digits, exact whitespace/wire limits, mutating input, and the
  malformed grammar/overflow matrix.

## Boundary

Current near-sdk-rs `U128` uses serde JSON strings and Rust `u128::from_str`, accepting forms such
as leading `+` and leading zeros; generated wrappers may also ignore unknown fields. This closed
ProofForge policy intentionally rejects those noncanonical forms. It is not serde-compatible,
generic JSON, or a public FT method, and does not yet parse receiver or memo fields.
