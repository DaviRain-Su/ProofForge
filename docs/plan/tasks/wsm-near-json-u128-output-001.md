---
id: wsm-near-json-u128-output-001
scope: wasm
status: done
depends-on: [wsm-near-output-001, wsm-near-nep141-event-001]
---

# wsm-near-json-u128-output-001 specialized quoted-u128 JSON view output

## Objective

Add the smallest public-standard ABI prerequisite: exact full-u128 quoted-decimal JSON view
output, without adding JSON input, objects, optional values, or a generic JSON serializer.

## Delivered

- Extracted `UInt128` constructors expose exactly ordered `(w0, w1)` scalar leaves. Other
  two-field structures remain ordinary records and do not select this codec.
- NEAR target lowering binds only view `.scalar .uint128` to canonical policy
  `near-json-u128-string-v1`; malformed frames fail closed. The policy is part of canonical program
  identity and therefore the registry digest. A later separately tested task extends this exact
  scalar policy to one compiler-owned mutation result shape.
- The emitter allocates an exact maximum 41-byte output and 39-byte scratch, writes opening and
  closing quotes, invokes the single shared two-limb decimal helper, and calls `value_return` once
  with exact length 3..41. Zero is `"0"`; nonzero output has no leading zero or NUL.
- Targeted and near-sandbox scenes pin 0, 2^64, 2^64+1, asymmetric limbs, and max u128 while the
  pre-existing raw UInt64 and bounded Borsh result bytes remain unchanged.

## Boundary

The wire bytes match current near-sdk canonical `U128` serialization needed by NEP-141/145
results. This slice does not parse JSON, validate AccountId input, serialize objects/null/bools,
or implement any public NEP method. Those remain schema-specialized follow-up slices.

See [wsm-near-json-u128-mutation-output-001](wsm-near-json-u128-mutation-output-001.md) for the
separate state-persisting mutation composition.
