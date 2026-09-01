# wsm-near-promise-then-001 — NEAR static self-callback edge

Status: done

Depends on: [wsm-near-promise-002](wsm-near-promise-002.md),
[wsm-near-promise-result-001](wsm-near-promise-result-001.md)

## Scope

Add one closed child → self-callback edge through `Near.Sdk.Promises.callThenReturned`:

- retain a static child receiver/method, independently bounded child and callback Borsh argument
  frames, lossless u128 deposits, and explicit gas budgets;
- keep both nearcore Promise indexes inside one target effect rather than exposing the Runtime
  stubs' dummy UInt64 as a source-level handle;
- create the child with `promise_batch_create` plus its function-call action;
- obtain the callback receiver from `current_account_id`, bound its register length to 64 bytes,
  and copy it to dedicated writable invocation scratch before the Promise calls;
- create the dependency with `promise_batch_then(child, self)` and append the callback action only
  to the returned callback index;
- preserve the separation between ordinary callback arguments and dependency results exposed by
  `promise_results_count` / `promise_result`;
- persist caller state before the final `promise_return(callback)` and reject views or a second
  returned Promise on the same execution path.

This slice fixes the callback receiver to the current contract. It deliberately does not add a
general Promise-handle builder, parallel joins, typed result decoding, or a private callback entry
guard. Until that guard lands, callback fixture entries remain directly callable and are not a
production lifecycle policy.

## Verification

- `Tests.NearPromiseSpec` pins extraction/canonicalization, independent frame geometry, exact
  `promise_batch_then` and `current_account_id` imports, child/action/then/callback ordering,
  callback-index return after state persistence, conditional import pruning, and view rejection.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies on near-sandbox 2.13.0 that a successful child supplies
  exact bytes separately from callback input, a missing child still runs a status-2 callback, and
  an eight-byte successful result reports length eight / `fits = false` to a four-byte descriptor
  without truncation. All three scenes return the callback's final value and commit its state.

## Next

Exact Borsh UInt64 result decoding over `ResultBuffer` is complete in
[wsm-near-promise-codec-001](wsm-near-promise-codec-001.md), and private self-callback entries now
use full current/predecessor AccountId equality in
[wsm-near-promise-private-001](wsm-near-promise-private-001.md). Static native transfer actions are
complete in [wsm-near-promise-transfer-001](wsm-near-promise-transfer-001.md); parallel
`promise_and` is complete in [wsm-near-promise-and-001](wsm-near-promise-and-001.md).
