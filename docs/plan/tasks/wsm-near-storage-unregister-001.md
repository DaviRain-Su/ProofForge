---
id: wsm-near-storage-unregister-001
scope: wasm
status: done
depends-on: [wsm-near-storage-registration-001]
---

# wsm-near-storage-unregister-001 closed zero-balance caller unregister

## Objective

Add the smallest caller-only registration lifecycle step: remove and refund an exact present-zero
registration without implementing force-unregister, public NEP-145 JSON methods, or ledger supply
burn.

## Delivered

- `unregisterCaller` is payable and checks exact attached deposit `(w0=1,w1=0)` before lookup,
  matching near-sdk-rs's one-yocto security guard. Missing returns false and retains that yocto.
- The caller's specialized map value must be present, fit, exactly 16 bytes, and decode to zero in
  both limbs. Malformed and nonzero values panic before `storage_remove`.
- The policy samples `storage_usage` immediately around removal, requires a positive unsigned
  reclaim, checks full-u128 `reclaimed × trusted perByteCost`, checks `cost + 1`, and stages one
  detached transfer to the complete dynamic caller AccountId.
- Real near-sandbox scenes cover deposit 0/2 guards, missing false, short and maximum-length key
  reclaim, exact transfer receipt amount/receiver, malformed/nonzero rejection, canonical key
  removal, and rollback of a post-remove full-u128 multiplication overflow. Fixture-only seed and
  max-cost methods construct malformed/nonzero/overflow states without broadening the SDK API.

## Policy and atomicity boundary

Current near-sdk-rs unregister refunds its configured fixed maximum registration amount plus the
attached yocto. ProofForge intentionally refunds this caller key's live measured reclaim at the
same explicit trusted price used by registration. Trie/account interactions therefore must not be
described as a universal fixed charge; the sandbox reverses isolated insertions in reverse order.

Every synchronous failure after removal lowers to a contract panic and relies on nearcore's atomic
executing-receipt rollback to restore the key, state, balance, and staged receipts. Once the method
receipt succeeds, a later detached refund receipt failure is asynchronous and cannot restore the
removed key; this matches the existing detached-transfer honesty boundary. The missing result may
rewrite ProofForge's fixed diagnostic state envelope, but it never writes or removes a map key.

## Not included

Arbitrary-account registration, storage withdrawal,
public NEP-145/JSON ABI, registration enforcement in ledger methods, protocol-price discovery, or
synchronous guarantee of detached receipt delivery. The separate
wsm-near-storage-force-unregister-001 slice now adds only caller nonzero-balance removal/supply burn.
