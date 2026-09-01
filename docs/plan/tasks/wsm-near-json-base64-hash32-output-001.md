---
id: wsm-near-json-base64-hash32-output-001
scope: wasm
status: done
depends-on: [wsm-near-output-001]
---

# wsm-near-json-base64-hash32-output-001 exact NEP-148 hash scalar

## Objective

Add the smallest missing wire prerequisite for NEP-148 metadata without exposing a generic Base64,
byte-vector, JSON-string, or `ft_metadata` API.

## Delivered

- Compiler-owned `Base64Hash32Result` is exactly four little-endian UInt64 leaves, representing the
  exact 32 raw bytes required by a present NEP-148 `reference_hash`. Ordinary four-field records do
  not bind to the nominal schema.
- View-only canonical policy `near-json-base64-hash32-v1` emits one quoted RFC 4648 STANDARD Base64
  string: opening quote at buffer 0, content at 1..44 with the final `=` at buffer 44, closing quote
  at 45, and exactly one `value_return` over the exact 46-byte arena. STANDARD alphabet bytes never
  receive optional JSON slash escaping, and no BOM or line ending is emitted.
- Structural and real nearcore tests pin the packed byte order and exact encoding of bytes 0..31:
  leaf `i` holds bytes `8i..8i+7` with byte `8i` least significant. Sequential, all-zero, and
  all-`0xff` vectors cover ordering, alphabet extremes including `/`, padding, independent decode,
  exact bytes, and view state freedom.

## Compatibility boundary

This is the serializer shape of near-sdk's `Base64VecU8` for one exact 32-byte value. It does not
implement `FungibleTokenMetadata`, optional-field coupling, `assert_valid`, arbitrary byte lengths,
or NEP-148 by itself. The following metadata-object slice owns ProofForge's explicit bounded string
capacities; those capacities are product limits, not authoritative near-contract-standards bounds.
