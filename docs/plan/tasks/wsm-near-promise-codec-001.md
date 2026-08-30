# wsm-near-promise-codec-001 — NEAR strict callback Borsh UInt64 decode

Status: done

Depends on: [wsm-near-promise-result-001](wsm-near-promise-result-001.md),
[wsm-near-promise-then-001](wsm-near-promise-then-001.md)

## Scope

Add one exact typed callback-result decoder through
`Near.Sdk.Promises.ResultBuffer.borshUInt64D`:

- consume the invocation-local descriptor established by the immediately preceding `read`;
- require nearcore status 1, `fits = true`, and exact length 8 before reading any byte;
- reconstruct all eight bytes as canonical little-endian Borsh `UInt64`;
- return an explicit source-selected fallback for not-ready, failed, oversized, or wrong-length
  results;
- project the decoder as a NEAR target value intrinsic so it composes with a mutating callback's
  state-plus-result CFG without introducing Borsh policy into Core;
- emit no new host import: the intrinsic reuses the checked status/length/fits/byte descriptor
  helpers over `promise_result`'s copied register.

This slice is deliberately UInt64-only. Bool canonicality and the remaining fixed-width scalar
family require their own source/extractor contracts; generic Borsh, dynamic aggregates, Promise
joins, and callback-entry authentication remain outside this slice.

## Verification

- `Tests.NearPromiseSpec` pins three extracted decoder values (capacities 8, 8, and 4), canonical
  target digest, exact status/fits/length guards, all eight byte lanes, high-lane shift 56, and
  explicit success/failure/oversized fallbacks.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies on near-sandbox 2.13.0 that a successful child decodes
  to UInt64 123 while callback argument 77 remains separate, and that failed and oversized child
  results both return fallback 999 while their callbacks still commit state.

## Next

Callback entries now authenticate full predecessor/current AccountId equality in
[wsm-near-promise-private-001](wsm-near-promise-private-001.md). Parallel `promise_and`, transfer
actions, and broader result codecs remain independent follow-up slices.
