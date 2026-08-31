---
id: wsm-near-storage-balance-of-001
scope: wasm
status: done
depends-on: [wsm-near-storage-balance-output-001, wsm-near-storage-registration-001, wsm-near-json-account-input-001]
---

# wsm-near-storage-balance-of-001 variable caller-registration balance view

## Objective

Compose the bounded AccountId input and optional `StorageBalance` output policies with the existing
`BAL2` registration map, without inventing a withdrawable balance or claiming complete NEP-145 ABI
compatibility.

## Delivered

- Exact `storage_balance_of` reads one canonical
  `BAL2 || u32_le(AccountId.length) || active AccountId` key and accepts only an exact 16-byte
  present balance value. Missing returns `null`; malformed present values fail the view.
- A present entry returns exact
  `{"total":"<cost>","available":"0"}`. Cost is checked full-u128
  `(AccountId.length + 64) × trustedPerByteCost`, where 64 is the current nearcore record geometry:
  Prefix4(4), Borsh length(4), NearToken(16), and `num_extra_bytes_record`(40).
- The view performs no storage writes, logs, or Promise effects. Zero trusted price or cost
  multiplication overflow fails closed rather than exposing a plausible but false balance.
- Structural and real nearcore tests cover missing, separately measured short/max AccountIds,
  escaped input, malformed storage, overflow, exact bytes, and state-write freedom.

## Boundary

This closed policy reports each account's actual variable registration cost and immediately refunds
all excess, so `available` is always zero. Current near-contract-standards instead measures a
maximum-length AccountId once at construction and reports that fixed configured minimum for every
registered account. ProofForge's input is also a bounded canonical JSON subset (unknown fields
rejected, 32 structural whitespace bytes, 433-byte wire maximum), narrower than serde. Therefore
the export has official shape and exact output bytes but is not claimed as full NEP-145 ABI or
economic-policy compatibility. This slice adds no `storage_balance_bounds`, deposit, withdraw,
unregister, arbitrary-account mutation, or automatic ledger registration enforcement.
