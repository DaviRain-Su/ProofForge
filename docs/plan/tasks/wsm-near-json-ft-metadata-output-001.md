---
id: wsm-near-json-ft-metadata-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-base64-hash32-output-001]
---

# wsm-near-json-ft-metadata-output-001 bounded metadata object output

## Objective

Compose the already verified JSON string escaping and exact 32-byte Base64 hash into one closed,
diagnostic metadata output prerequisite without exporting `ft_metadata` or generic JSON support.

## Delivered

- Compiler-owned `FungibleTokenMetadataResult` has exactly 70 UInt64 leaves: packed name9,
  symbol3, optional icon34, optional reference18, optional hash5, and decimals1. The nominal schema
  alone binds `near-json-ft-metadata-bounded-v1(name=64,symbol=16,icon=256,reference=128,hash=32)`.
- The view-only serializer emits exact field order `spec,name,symbol,icon,reference,reference_hash,
  decimals`, fixed spec `ft-1.0.0`, explicit null options, distinct Some-empty strings, shared JSON
  escaping and shared RFC4648 STANDARD Base64, bare decimals 0..255, and one `value_return`.
- One exact 2929-byte arena covers the worst case. Active UTF-8 is validated; every inactive and
  partial-word byte must be zero. Small repeated helpers keep generated functions under nearcore's
  control-block bound.
- Structural and real-nearcore tests cover all four reference/hash presence combinations,
  NUL/control/quote/backslash/raw Unicode, empty and max capacities, all-zero/all-ff hashes,
  decimal width transitions, malformed lengths/presence/UTF-8/padding, stale isolation, and view
  state freedom.

## Compatibility boundary

Near-contract-standards does not impose lengths on name, symbol, icon, or reference. The
64/16/256/128 decoded-byte capacities are explicit ProofForge product limits, not NEP-148 bounds.
This codec does not automatically call `assert_valid`: it does not enforce reference/hash matching,
while a present hash is already exactly 32 bytes by frame geometry. No standard export or complete
NEP-148 ABI compatibility is claimed.
