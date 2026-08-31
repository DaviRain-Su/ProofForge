---
id: wsm-near-ft-resolve-transfer-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-resolve-input-001, wsm-near-promise-json-u128-result-001, wsm-near-json-u128-mutation-output-001, wsm-near-ft-transfer-001]
---

# wsm-near-ft-resolve-transfer-001 private fungible-token resolver

## Objective

Compose the bounded callback argument and Promise-result codecs with the integrated `BAL2` ledger
as an exact private `ft_resolve_transfer` reconciliation operation, without prematurely exporting
`ft_transfer_call`.

## Delivered

- The exact export is private and non-payable, accepts the compiler-owned 20-leaf resolver frame,
  requires exactly one Promise result, and reads dependency index zero. Failed, oversized, or
  strict-codec-invalid output requests the full amount; valid unused amounts clamp to the original
  transfer.
- A missing or present-zero receiver performs no balance write or event and returns the original
  amount. Positive refunds preserve receiver registration. A still-registered sender receives the
  checked refund, supply remains unchanged, one `ft_transfer` event carries memo `refund`, and the
  returned used amount is `amount - refund`.
- If the sender was deleted, the receiver is debited, supply is checked and reduced, one `ft_burn`
  event carries memo `refund`, and the original amount is returned as used. This branch difference
  follows current near-contract-standards.
- Promise status/result validation, balance shape reads, clamp, and all u128 arithmetic finish
  before writes. Malformed balances, sender credit overflow, supply underflow, wrong result count,
  private/non-payable failures, and synchronous post-write traps rely on nearcore transaction
  rollback. Asynchronous receipt failure is not claimed to roll back an earlier transfer.

## Verification and compatibility boundary

Extraction/WAT checks pin private → non-payable → input ordering, one result-count/index-zero read,
read-before-write branches, no removal, at most one event, state persistence, and three canonical
quoted-u128 returns. Near-sandbox runs genuine child → private callback receipts for valid, failed,
malformed, oversized, clamp, no-op, transfer-refund, deleted-sender burn, and rollback paths.

Arguments remain `near-json-ft-resolve-args-bounded-v1`, and successful result decoding remains the
strict canonical quoted-decimal subset. Both are narrower than near-sdk serde_json, so this exact
operation/event policy is not a claim of complete public NEP-141 ABI compatibility. The scheduling
fixtures are nonstandard and do not implement `ft_transfer_call`.

## Next

Compose the dynamic weighted `ft_on_transfer` child call with a returned private resolver callback,
then expose `ft_transfer_call` only after transfer-before-call state and receipt semantics are pinned.
