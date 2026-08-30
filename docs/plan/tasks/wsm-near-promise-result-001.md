# wsm-near-promise-result-001 — NEAR bounded callback-result substrate

Status: done

Depends on: [wsm-near-promise-002](wsm-near-promise-002.md),
[wsm-near-memory-001](wsm-near-memory-001.md)

## Scope

Add independently bounded callback-result observation before Promise chaining:

- expose invocation-local `Promises.resultsCount` through nearcore's
  `promise_results_count() -> u64`;
- expose `Promises.ResultBuffer.read(index)` through
  `promise_result(index, dedicated_register) -> u64` with a compile-time 1..64 byte capacity;
- preserve nearcore's exact status values: 0 not ready, 1 successful, 2 failed, while trapping
  unknown values and retaining nearcore's abort for an index outside `resultsCount`;
- reset a separate invocation-local result descriptor before every host read;
- consult register length and bytes only for status 1, because statuses 0/2 leave the selected
  register untouched and potentially stale;
- report an oversized successful result's actual length with `fits = false` and perform no
  allocation or register copy;
- expose status, length, fits, and bounds-checked byte leaves without exposing guest pointers;
- reject both result count and result reads in views, matching nearcore.

Status 0 remains represented for forward ABI compatibility even though current protocol callback
execution does not produce `NotReady`. Statuses 0/2 use neutral `length = 0`, `fits = true`, and no
readable bytes; callers must branch on status before interpreting metadata.

Promise chaining (`promise_then`/batch-then), joins, typed Borsh result decoding, private callback
entry guards, and native transfer remain outside this slice itself.

## Verification

- `Tests.NearPromiseResultSpec` pins extraction/canonical forms, both exact host signatures,
  conditional import pruning, dedicated register 4, descriptor reset, status validation, success-
  only register inspection, bounded allocation/copy, byte gating, and view rejection.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromiseResult` fixture.
- `runtime-tests/near/promise-result.sh` verifies on near-sandbox 2.13.0 that an ordinary mutating
  call reports count zero and an out-of-range `promise_result(0, ...)` aborts without state change.
- Genuine success, failed-child, and oversized callback inputs require the next chaining slice and
  are deliberately not simulated as ordinary calls.

## Next

One static `promise_batch_then` self-callback edge and its genuine near-sandbox success/failure/
oversized matrix are complete in
[wsm-near-promise-then-001](wsm-near-promise-then-001.md). Add typed bounded Borsh result decoding
and private self-callback guards next.
