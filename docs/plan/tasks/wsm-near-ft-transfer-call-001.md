---
id: wsm-near-ft-transfer-call-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-transfer-call-input-001, wsm-near-ft-transfer-001, wsm-near-promise-ft-resolve-chain-001]
---

# wsm-near-ft-transfer-call-001 integrated fungible transfer call

## Objective

Compose the bounded four-field argument frame, integrated `BAL2` transfer/event, specialized
weighted child call, and private resolver behind the exact `ft_transfer_call` export without
claiming broader JSON compatibility.

## Delivered

- The payable entry requires exactly one yoctoNEAR, a positive amount, distinct predecessor and
  receiver, and present exact-16-byte balances for both accounts. Both reads and checked two-limb
  subtraction/addition finish before source-then-receiver writes; supply remains unchanged.
- The initial exact NEP-141 transfer event follows both writes. Missing/null memo omits `memo`, while
  Some-empty and bounded UTF-8 values retain it. The specialized dynamic receiver call then sends
  exact `ft_on_transfer` JSON with zero deposit, gas/weight 0/1 and chains the private resolver on
  this contract with zero deposit, 5 Tgas, and weight zero.
- State persistence precedes `promise_return` of the callback receipt. The outer SuccessValue is
  therefore the resolver's quoted used amount: partial refunds return `amount - refund`; full,
  malformed, and failed child results reconcile through the existing exact resolver policy.

## Verification and compatibility boundary

Targeted IR/WAT checks pin guard/read/read/write/write/event ordering, exact host DAG and gas/weight,
unchanged supply fields, state persistence before one returned callback per memo branch, and no
ordinary `value_return`. Near-sandbox covers pre-effect failures plus genuine partial/full/
malformed/failed child receipts, exact initial/refund event sequence, quoted result bytes,
present-zero retention, rollback, and conservation.

The operation, event, Promise, resolver, and output behavior follows the pinned
near-contract-standards path. Input still uses
`near-json-ft-transfer-call-args-bounded-v1` (1179 wire bytes, 32 structural whitespace bytes, raw
known keys, unknown-field rejection, AccountId/message/memo capacities). It is narrower than the
generated serde_json wrapper and is not a claim of complete public NEP-141 ABI compatibility.
