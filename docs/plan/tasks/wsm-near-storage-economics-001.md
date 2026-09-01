---
id: wsm-near-storage-economics-001
scope: wasm
status: done
depends-on: [wsm-near-storage-001]
---

# wsm-near-storage-economics-001 dynamic storage usage

## Objective

Expose nearcore's real invocation-dynamic storage usage before designing registration economics,
without guessing a storage price or adding a public registration ABI.

## Delivered

- `Near.Runtime.storageUsage` and `Near.Sdk.Context.storageUsage` lower through the complete target
  path to the conditional `env.storage_usage : () -> i64` import. The unsigned result is the current
  contract storage usage in bytes and includes earlier storage effects in the same invocation.
- The fixture samples immediately around writes/removes. It demonstrates positive stable views,
  same-size replacement delta zero, exact value/key-length deltas, absent removal delta zero, and
  full insert/remove reclamation without pinning nearcore's internal trie-record overhead.
- The host leaf is available in both view and mutation methods. View execution can observe usage
  but cannot persist writes; receipt failure continues to roll back storage effects.

## Authoritative boundary

Current near-sdk-rs `env::storage_usage` directly wraps the VM `storage_usage` host function and
returns `StorageUsage = u64`; nearcore 2.13.0 exposes the same no-argument i64 import. Neither
current near-sdk-rs nor nearcore exposes an `env.storage_byte_cost` guest import. Storage price is
the protocol-config `storage_amount_per_byte` and can vary by protocol version or custom chain.
ProofForge therefore does not expose or hard-code the commonly deployed `10^19` yoctoNEAR value.
A future charging policy must accept an explicit trusted network/config value.

## Not included

Storage registration, refunds, deposits, a byte-cost constant/API, public JSON methods, or FT
method compliance.
