# wsm-near-promise-and-001 — NEAR ordered two-child Promise join

Status: done

Depends on: [wsm-near-promise-then-001](wsm-near-promise-then-001.md),
[wsm-near-promise-private-001](wsm-near-promise-private-001.md),
[wsm-near-memory-001](wsm-near-memory-001.md)

## Scope

Add one closed parallel graph through `Near.Sdk.Promises.callAndThenReturned`:

- schedule exactly two independently bounded static function calls in left/right source order;
- retain each concrete host Promise index, stage them as two consecutive little-endian u64 words in
  one aligned 16-byte arena span, and immediately call `promise_and(ptr, 2)`;
- use the joint Promise only as the dependency of `promise_batch_then`; never append an action to it
  or pass it directly to `promise_return`;
- append one static authenticated self-callback action and return only that callback receipt after
  caller-state persistence;
- preserve flattened callback-result order as left index 0 and right index 1, including status-2
  failures, and read both results independently;
- reject views and a second returned Promise on the same execution path, while pruning
  `promise_and` from modules that do not join.

This slice intentionally exposes no source-level Promise handles. Arbitrary-N and nested joins,
bare joint-Promise return, transfer joins, dynamic AccountId values, and multi-action builders
remain outside the contract.

## Verification

- `Tests.NearPromiseSpec` pins extraction/canonicalization, exact host import, 16-byte/8-aligned join
  storage, concrete left/right index stores at offsets 0/8, create/action/and/then/action ordering,
  callback-only return after state persistence, ordered result reads, view rejection, and import
  pruning.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies on near-sandbox 2.13.0 that two successes retain order,
  either failed child still releases the callback, and the unaffected child result is observed
  without short-circuiting.

## Next

Do not generalize this closed graph into arbitrary-N or nested joins until a source-visible Promise
handle/lifecycle contract defines legal action append, dependency, and return states. Broader typed
callback codecs and entry lifecycle metadata remain independent slices.
