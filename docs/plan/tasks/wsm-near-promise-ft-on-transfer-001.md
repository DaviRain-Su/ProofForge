---
id: wsm-near-promise-ft-on-transfer-001
scope: wasm
status: done
depends-on: [wsm-near-json-message-input-001, wsm-near-promise-account-transfer-001, wsm-near-json-u128-output-001]
---

# wsm-near-promise-ft-on-transfer-001 specialized weighted FT child call

## Objective

Add the smallest reusable dynamic Promise prerequisite for a future `ft_transfer_call`: create and
return one weighted `ft_on_transfer` child receipt with an exact compiler-owned payload. Do not add
a callback, resolver, generic JSON Promise API, or standard `ft_transfer_call` export.

## Authoritative boundary

- Current near-contract-standards serializes receiver arguments in exact field order
  `sender_id`, `amount`, `msg`; `amount` is a quoted decimal `U128` and the method is
  `ft_on_transfer` with zero attached deposit.
- Current near-sdk-rs `Promise::function_call_weight` lowers to
  `promise_batch_action_function_call_weight(promise_index, method_len, method_ptr, args_len,
  args_ptr, amount_ptr, gas, weight)`. nearcore 2.13.0 exposes that exact eight-u64 host ABI.
- Gas weight apportions unused gas. This closed operation uses exact gas 0 and weight 1;
  it does not model a general Promise builder.

## Delivered

- `Promises.ftOnTransferReturned` accepts complete dynamic receiver/sender `AccountId` carriers,
  lossless two-limb `NearToken`, and compiler-owned `BoundedMessage64`. Geometry is 2..64 bytes;
  Context accounts are nominally syntax-valid, while manually constructed carriers receive only
  this geometry guarantee. Receiver staging writes active raw bytes only, with no JSON/Borsh prefix.
- The emitter allocates the exact 844-byte worst-case payload arena: 37 structural bytes, two
  independently escaped 64-byte strings, and 39 decimal digits. Shared JSON escaping and u128
  decimal helpers produce exact active bytes; packed message extraction masks each byte by `0xff`.
- Host effects are ordered create → weighted function-call action. The 16-byte deposit frame is
  exact zero; payload UTF-8 validation precedes creation, and `promise_return` follows caller-state
  persistence. NEAR commits the caller's state and Promise effects atomically at receipt end; a
  later child receipt failure is asynchronous and does not retroactively roll back that receipt.
- Targeted IR/WAT pins the fixed method, conditional weighted import and ABI argument order,
  payload/deposit geometry, dynamic inactive-padding isolation, one action/return, view rejection,
  and rejection of receiver lengths 1/65. Existing static calls and dynamic native transfers retain
  their own unweighted/transfer host paths.
- The near-sandbox 2.13.0 observer fixture returns `deposit16 || input` and proves exact sender,
  mixed/high u128 decimal, empty/control/Unicode/max-64 message payloads, zero deposit, returned
  receipt execution, and asynchronous failure for an absent dynamic receiver.

## Boundary

This is internal closed Promise composition. `BoundedMessage64` still comes from a bounded canonical
JSON subset rather than unrestricted serde_json. Promise-result U128 decoding, callback/private
guards, resolver ledger policy, positive-amount/registration/ledger checks, and the public
`ft_transfer_call` method remain later slices. This operation itself does not debit a balance.
