---
id: wsm-near-u128-storage-001
scope: wasm
status: done
depends-on: [wsm-near-u128-001, wsm-near-storage-001]
---

# wsm-near-u128-storage-001 exact Borsh NearToken values

## Objective

Add the lossless storage-value codec needed before an internal NEP-141 ledger, without adding
AccountId collection keys, balances, supply, or public FT methods.

## Delivered

- `borshNearToken` writes exactly 16 little-endian bytes: all of `w0`, then all of `w1`.
- `resultNearTokenW0D/W1D` decode the active storage result only when status is present, the
  register fits, and length is exactly 16. Each limb otherwise returns its explicit fallback.
- The fixture uses one raw fixed key to prove insert/replacement/removal status, state write-last,
  stored zero versus absence, same-invocation stale-register isolation, and byte-exact persistence.
- Ordinary 8-byte and bounded 20-byte writes exercise malformed exact-length and uncopied
  oversized paths without test-only storage injection.

## Verification

- Targeted extraction pins 16-byte reads/writes, 8/20-byte malformed writes, operation order,
  canonical digest, and WAT storage/shift/or instructions.
- near-sandbox checks mixed and maximum limbs, exact durable bytes, full fallback behavior,
  actual result length/fits status, zero presence, and key reclamation.

## Not included

Full AccountId Identity keys, collection hashing, a typed balance map, total supply, ledger policy,
events, public methods, JSON ABI, storage management, or NEP-141 contract compliance.
