---
id: wsm-near-ft-receiver-value-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-on-transfer-input-001, wsm-near-json-u128-mutation-output-001]
---

# wsm-near-ft-receiver-value-001 immediate-value FT receiver

## Objective

Compose the bounded receiver-argument policy and mutating quoted-u128 output into an exact
`ft_on_transfer` export whose closed behavior immediately rejects the full transferred amount.

## Delivered

- `NearFtReceiverValue.ft_on_transfer` is non-payable and accepts the compiler-owned 20-leaf
  `FtOnTransferArgs` frame. On success it persists an independent call counter and returns the
  input amount unchanged as exact quoted-decimal U128 bytes.
- Returning the full amount implements only `PromiseOrValue::Value(amount)`: this closed receiver
  rejects all transferred tokens. It does not yet model receiver business logic or the Promise
  branch.
- IR/WAT checks pin the bounded input and quoted-u128 output policies, exact snake-case export,
  deposit guard before input/effects, state persistence before the single `value_return`, and the
  absence of logs and `promise_return`.
- near-sandbox verifies mixed/high-limb output bytes, successful persistence, non-payable and parse
  rollback, and a genuine dynamic weighted `ft_on_transfer` child whose returned receipt exposes
  the receiver's quoted amount.

## Boundary

The observable immediate-value output matches near-sdk `PromiseOrValue::Value(U128)`, but input is
still ProofForge's 1071-byte bounded canonical subset rather than full generated serde behavior.
This slice therefore does not claim complete NEP-141 receiver ABI compatibility. Supporting both
immediate U128 and returned Promise terminals requires a separate compiler-owned output carrier.
