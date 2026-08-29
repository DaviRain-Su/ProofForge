# wsm-near-promise-001 — NEAR detached static Promise function call

Status: done

Depends on: [wsm-near-iterable-001](wsm-near-iterable-001.md)

## Scope

Add the first closed cross-contract call through `Near.Sdk.Promises.callDetached`:

- receiver and method are compile-time strings; AccountId validation enforces 2..64 ASCII bytes,
  lowercase alphanumeric components separated by single `-`, `_`, or `.`, and method names enforce
  1..256 UTF-8 bytes;
- arguments use the existing `BoundedBytes` frame with compile-time capacity `1..64`;
- attached deposit is lossless `NearToken` u128 and gas is explicit UInt64;
- lowering matches near-sdk-rs's function-call path: `promise_batch_create` followed by
  `promise_batch_action_function_call`;
- Promise indexes are preserved in generated locals rather than assuming index zero;
- the emitter stages deposit as exact 16-byte little-endian low/high limbs in the checked arena and
  places static receiver/method bytes in a deterministic region beginning at address 8192;
- Promise creation is rejected in views.

The call is deliberately detached: it does not emit `promise_return`, so remote success, failure,
or returned bytes do not become the current method's result. Receipt scheduling still participates
in nearcore transaction semantics: synchronous host validation traps roll back the caller, a caller
panic discards staged outgoing receipts, and a later remote failure does not roll back already
committed caller state.

Promise forwarding, chaining, callbacks/results, joins, native transfer, dynamic receiver/method
values, and dynamic unbounded arguments are outside this slice.

## Verification

- `Tests.NearPromiseSpec` pins literal validation, exact extracted effects, per-method lowering,
  host imports, static-data offsets, arena-backed u128 staging, explicit gas, absence of
  `promise_return`, view rejection, and canonical digest.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` deploys the fixture as caller and receiver on near-sandbox 2.13.0
  and verifies exact UInt64 arguments, deposit limbs for `2^64 + 7`, zero deposit, detached remote
  failure, caller-panic receipt discard, and synchronous insufficient-balance rollback.

## Next

Add an explicit returned/forwarded static function call using `promise_return`. Keep callback result
inspection and `promise_then` in a subsequent slice so forwarding semantics remain independently
testable.
