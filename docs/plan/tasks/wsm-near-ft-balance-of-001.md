---
id: wsm-near-ft-balance-of-001
scope: wasm
status: done
depends-on: [wsm-near-json-account-input-001, wsm-near-json-u128-output-001, wsm-near-fungible-ledger-001]
---

# wsm-near-ft-balance-of-001 specialized bounded balance view

## Objective

Compose the existing schema-specialized AccountId JSON input and quoted-u128 output into an exact
`ft_balance_of` export backed by the closed ledger's canonical `BAL2` map, without opening a
generic JSON ABI or adding mutating FT methods.

## Delivered

- The exact snake-case export accepts one compiler-owned AccountId through policy
  `near-json-account-id-object-bounded-v1(max-wire=433,ws=32,keys=canonical,unknown=reject)` and
  returns policy `near-json-u128-string-v1`.
- The view stages `BAL2 || u32_le(length) || active account bytes`, performs one logical storage
  read, and decodes only missing or an exact fitting 16-byte `w0_le || w1_le` value. Missing and
  exact present zero both serialize as `"0"`; malformed present values trap before output.
- Extraction, target IR, canonical digest, WAT, and sandbox gates pin the combined input/output
  wrapper, exact export, one `value_return`, no state writes/logs/promises, mixed/high/max decimal
  results, raw and escaped short/64-byte identities, inactive-padding independence, and stale
  register isolation after malformed 8/20-byte values.
- Fixture-only seed entries create present-zero, malformed, short, and maximum identities for
  runtime diagnosis. They do not extend the SDK contract or create another balance namespace.

## Boundary

The method shape and successful wire bytes match NEP-141 `ft_balance_of`, but its input parser is
the documented bounded canonical subset rather than near-sdk-rs serde_json: unknown and escaped
field names are rejected, aggregate structural whitespace is capped, and wire size is capped at
433. This slice therefore does not claim full NEP-141 compliance. It adds no `ft_total_supply`,
mutating FT method, generic JSON codec, registration enforcement, resolver, event, or Promise.
