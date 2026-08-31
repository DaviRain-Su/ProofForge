---
id: wsm-near-storage-registration-001
scope: wasm
status: done
depends-on: [wsm-near-storage-economics-001, wsm-near-u128-mul-001, wsm-near-promise-account-transfer-001, wsm-near-account-token-map-001]
---

# wsm-near-storage-registration-001 closed measured caller registration

## Objective

Compose the completed storage, arithmetic, deposit, AccountId-map, and dynamic-transfer boundaries
into one closed caller-only registration policy without claiming the public NEP-145 ABI.

## Delivered

- `Near.Sdk.Fungible.Registration` supplies pure descriptor/config/cost gates. The fixture accepts
  an immutable trusted full-width per-byte price profile; it does not read or guess a chain price.
- `registerCaller` validates caller geometry and config before effects, reads the exact map value,
  inserts a present 16-byte zero only when missing, and samples `storage_usage` immediately around
  that caller's variable-length canonical key. Checked u128×u64, compare, and subtraction precede
  a positive-excess detached refund to the complete caller AccountId.
- A well-formed duplicate performs no map write and refunds its full nonzero deposit. Malformed
  present values fail closed. Zero is a present registration value and is not missing.
- Sandbox scenes pin short/max-length caller deltas, exact retained cost and refunds, malformed
  rejection, and no key/state/balance residue after insufficient deposit, zero config, or cost
  multiplication overflow.

## Atomicity boundary

The exact delta cannot be known before nearcore performs the variable-key insert. The insert is
therefore speculative. Every failure after it is a contract panic; safety depends on NEAR's atomic
rollback of the executing receipt, including storage, state, balance, and newly staged receipts.
Returning a source-level `Except.error` is safe here only because the NEAR emitter lowers it to that
panic path. All checks that can run before insertion do so.

## Not included

Public NEP-145/JSON methods, arbitrary-account registration, unregister/force-unregister, storage
withdrawal, protocol-price discovery, automatic ledger enforcement, resolver, or FT method ABI.
