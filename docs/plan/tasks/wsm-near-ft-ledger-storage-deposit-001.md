---
id: wsm-near-ft-ledger-storage-deposit-001
scope: wasm
status: done
depends-on: [wsm-near-ft-ledger-storage-views-001, wsm-near-storage-deposit-001]
---

# wsm-near-ft-ledger-storage-deposit-001 integrated registration

## Objective

Compose the verified payable bounded `storage_deposit` operation with the same BAL2 artifact that
owns fungible balances, without changing supply or creating a second registration map.

## Delivered

- Missing/null account defaults to predecessor; explicit accounts and `registration_only` use the
  existing bounded parser. New keys are present-zero BAL2 balances.
- New registration measures the live nearcore storage delta, charges it at the artifact's immutable
  one-yocto-per-byte fixture profile, and refunds positive excess to predecessor. Duplicate keys
  refund the full deposit. Supply is unchanged.
- Structural and real-nearcore tests pin parser/read/write/usage/refund/output composition, exact
  StorageBalance bytes, predecessor-targeted refund receipts, explicit-account/shared-map
  visibility, insufficient-deposit and malformed rollback, and all prior ledger behavior.

## Compatibility boundary

The parser rejects unknown fields and has bounded whitespace; the immutable fixture price is not a
network-price source. This preserves the existing variable-cost ProofForge policy and does not claim
complete NEP-145 ABI or economic compatibility. `registration_only` is intentionally accepted and
ignored like the selected stock FT policy; a later detached refund failure does not roll back the
already committed registration receipt.
