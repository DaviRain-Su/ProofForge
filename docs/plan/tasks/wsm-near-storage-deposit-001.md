---
id: wsm-near-storage-deposit-001
scope: wasm
status: done
depends-on: [wsm-near-json-storage-deposit-input-001, wsm-near-storage-balance-output-001, wsm-near-storage-registration-001]
---

# wsm-near-storage-deposit-001 variable-cost storage deposit

## Objective

Compose the bounded optional-account arguments, measured variable registration economics, and exact
StorageBalance output into one payable `storage_deposit` export over the canonical `BAL2` map.

## Delivered

- Missing/null `account_id` selects the predecessor; an explicit valid 2..64-byte AccountId selects
  that exact canonical key. `registration_only` missing/null/false/true is accepted and ignored,
  matching the stock FT's behavior. Refunds always target the predecessor.
- New registration speculatively inserts present zero, measures live `storage_usage`, checks the
  full-u128 trusted-price product and attached deposit, retains the exact variable cost, and refunds
  positive excess. A valid duplicate performs no write and refunds the full positive deposit.
- The mutation returns exact `{"total":"…","available":"0"}` bytes. Generic extraction now
  preserves exact compiler-owned boundary-record leaves after state writes, and the NEAR terminal
  admits this specific mutating output policy; ordinary records and other outputs remain rejected.
- Structural and real nearcore tests pin the 459-byte parser policy, read/write/refund ordering,
  state-before-output terminal, caller-default and explicit max-length keys, exact/high-limb output,
  duplicate and excess refunds, malformed values, insufficient deposits, zero price, multiplication
  overflow, and atomic rollback after speculative insertion.

## Boundary

ProofForge charges each target's measured `(AccountId.length + 64) × trustedPrice`; stock
near-contract-standards uses one configured fixed maximum-account cost. Its generated serde wrapper
also accepts unknown fields by default, while this bounded canonical subset rejects unknown and
escaped keys and limits structural whitespace. The export therefore has the official name and
operation/output semantics but is not claimed as complete NEP-145 ABI/economic compatibility.
There is still no storage-withdraw path, generic JSON codec, or automatic ledger registration
enforcement. A failed asynchronous refund receipt does not roll back the already successful call.
