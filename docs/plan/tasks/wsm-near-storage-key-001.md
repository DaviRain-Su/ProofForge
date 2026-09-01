---
id: wsm-near-storage-key-001
scope: wasm
status: done
depends-on: [wsm-near-storage-001]
---

# wsm-near-storage-key-001 exact internal storage-key geometry

## Objective

Reserve the lossless maximum key frame required by the next fixed-prefix AccountId Identity map,
without widening public Borsh ABI, storage values/results, event payloads, or promise arguments.

## Delivered

- Internal raw-storage key effects accept capacities 1..72. The maximum is exactly
  `Prefix4 || u32_le(AccountId byte length) || 64 active bytes`.
- Raw values and copied register results remain 1..64. Public bounded input/output remains 1..64;
  NEP-141 memo remains 16, and other bounded effects retain their existing owners and limits.
- The existing raw-storage fixture stages one exact 72-byte active key and proves insert, read,
  exact durable bytes, remove, and storage reclamation against near-sandbox.
- Extract, target IR, CFG well-formedness, and emitter staging use the key-only capacity predicate
  only at host storage key positions.

## Not included

AccountId key construction, map APIs, hashing, balances, supply, ledger policy, public FT methods,
JSON ABI, or NEP-141 contract compliance.
