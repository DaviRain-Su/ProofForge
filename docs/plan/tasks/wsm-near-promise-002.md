# wsm-near-promise-002 — NEAR returned static Promise function call

Status: done

Depends on: [wsm-near-promise-001](wsm-near-promise-001.md)

## Scope

Add explicit result forwarding through `Near.Sdk.Promises.callReturned`:

- retain promise-001's static receiver/method, bounded Borsh arguments, lossless u128 deposit,
  explicit gas, checked arena staging, and view rejection;
- share the exact `promise_batch_create` plus `promise_batch_action_function_call` lowering with
  detached calls while preserving the concrete Promise index in a generated local;
- emit nearcore's `promise_return(index)` only for returned calls;
- defer `promise_return` until after caller state persistence so it is the final return-setting host
  operation and cannot be overwritten by scalar `value_return`;
- reject a second returned Promise on the same execution path rather than silently replacing the
  first index;
- preserve detached behavior, including the absence of a `promise_return` import in a module that
  contains only detached calls.

This remains asynchronous forwarding. It does not synchronously wait for remote execution: a
successful child receipt supplies the final bytes, and a failed child receipt supplies the final
failure. State committed by the already-successful caller receipt remains committed if that later
child fails.

Promise chaining (`promise_then`), callbacks/result inspection, joins, native transfer, dynamic
receiver/method values, and dynamic unbounded arguments remain outside this slice.

## Verification

- `Tests.NearPromiseSpec` distinguishes detached and returned extraction/canonical forms, pins the
  conditional `promise_return` import/call, checks action → state persistence → return ordering,
  rejects scalar-return overwrite, view use, and two returned Promises on one path.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies exact forwarded 8-byte UInt64 success, caller and receiver
  commits, propagated missing-method failure with caller-receipt state retained, and all detached
  promise-001 rollback/failure scenes.

## Next

Bounded callback result count/status/read primitives are complete in
[wsm-near-promise-result-001](wsm-near-promise-result-001.md). Introduce `promise_then` next so
genuine callback success/failure/oversized-result scenes exercise that independently tested
substrate before typed decoding and private self-callback policy are added.
