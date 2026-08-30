# wsm-near-promise-transfer-001 — NEAR static native Promise transfer

Status: done

Depends on: [wsm-near-u128-001](wsm-near-u128-001.md),
[wsm-near-memory-001](wsm-near-memory-001.md),
[wsm-near-promise-002](wsm-near-promise-002.md)

## Scope

Add explicit native transfers through `Near.Sdk.Promises.transferDetached` and
`Near.Sdk.Promises.transferReturned`:

- accept a compile-time validated AccountId receiver and a lossless `NearToken` amount;
- allocate an aligned 16-byte invocation-local amount frame and store exact little-endian u128 low
  and high limbs;
- lower through `promise_batch_create(receiver)` followed by
  `promise_batch_action_transfer(promiseIndex, amountPtr)` while preserving the concrete Promise
  index;
- keep detached and returned lifecycle semantics explicit: detached transfer does not import or
  call `promise_return`, while returned transfer persists caller state before one final
  `promise_return(promiseIndex)`;
- conditionally import the transfer action without retaining the function-call action in a
  transfer-only module;
- reject transfers in views and reject a returned transfer combined with another returned Promise
  on the same execution path.

This slice deliberately keeps the receiver static. Dynamic AccountId values, reusable Promise
handles/builders, `promise_and`, multi-action batches, and transfer callbacks remain outside it.
The Runtime stages a receipt action; it does not model transfer as synchronous balance mutation.

## Verification

- `Tests.NearPromiseSpec` pins extraction counts, exact 16-byte/8-aligned amount allocation, low/high
  stores, host-call operand order, import pruning, create-before-action and
  action-before-state-before-return ordering, view rejection, and the one-return constraint.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies on near-sandbox 2.13.0 that detached `2^64 + 7` and
  returned `11` transfers change the receiver balance exactly, the returned receipt forwards an
  empty successful value, and an unaffordable max-u128 action fails synchronously with receiver
  balance and caller state unchanged.

## Next

The closed ordered two-child `promise_and` graph is complete in
[wsm-near-promise-and-001](wsm-near-promise-and-001.md). Dynamic AccountId, arbitrary-N/nested
joins, and general multi-action builders should follow only with an explicit source-level handle
and lifecycle contract; broader result codecs remain separate.
