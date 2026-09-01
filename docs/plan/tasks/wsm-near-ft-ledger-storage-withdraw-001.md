---
id: wsm-near-ft-ledger-storage-withdraw-001
scope: wasm
status: done
depends-on: [wsm-near-ft-ledger-storage-deposit-001, wsm-near-storage-withdraw-001]
---

# wsm-near-ft-ledger-storage-withdraw-001 integrated zero-available withdrawal

## Objective

Compose the verified bounded `storage_withdraw` boundary into the integrated BAL2 ledger without
inventing withdrawable balance where registration already refunded all excess.

## Delivered

- Exact one yocto plus missing/null/explicit-zero amount returns the predecessor's variable
  StorageBalance total and zero available. Positive amount, wrong deposit, missing/malformed
  registration, and malformed input fail closed.
- The method performs one strict BAL2 read and no map/supply mutation, removal, log, refund, or
  Promise action. The attached security yocto is retained like the selected stock behavior.
- Real-nearcore tests cover all accepted amount spellings, positive/wrong-deposit/missing rejection,
  exact output/state, no transfer receipt, and all prior ledger regressions.

## Compatibility boundary

The amount object remains ProofForge's bounded canonical subset and retained total uses the
immutable one-yocto-per-byte fixture profile. This is not a complete NEP-145 ABI/economics claim.
