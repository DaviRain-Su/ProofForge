# wsm-near-promise-private-001 — NEAR authenticated self-callback entries

Status: done

Depends on: [wsm-020](wsm-020.md),
[wsm-near-promise-then-001](wsm-near-promise-then-001.md),
[wsm-near-promise-codec-001](wsm-near-promise-codec-001.md)

## Scope

Authenticate the three `NearPromise` callback entries before they inspect dependency results:

- require `Near.Sdk.Access.isSelfCall` as the callback body's outermost guard;
- compare predecessor and current AccountId by exact byte length and all eight zero-padded UInt64
  words, rather than treating the legacy low word as an identity;
- keep the Promise-result read, decode, state persistence, and value return exclusively in the
  authenticated branch;
- reject an external predecessor through the existing fail-closed error path before any
  `promise_result` access or storage write;
- reuse the existing SDK AccountId/context surface and target leaves, with no new Runtime stub,
  target intrinsic, or host ABI.

This predicate authenticates a receipt whose immediate predecessor is the current contract, which
is the NEAR self-callback convention. It does not prove that a dependency result exists: a receipt
that the contract deliberately sends directly to itself also passes identity authentication and
must still satisfy the separate Promise-result status/read checks.

## Verification

- `Tests.NearPromiseSpec` pins both account-id host imports, exact length plus all eight word
  comparisons, predecessor/current reads before `promise_result`, and result access dominated by
  the authenticated branch with a panic-only rejection branch.
- Pinned `wat2wasm 1.0.41` assembles the registered `NearPromise` fixture.
- `runtime-tests/near/promise.sh` verifies on near-sandbox 2.13.0 that an external
  `test.near → receiver.test.near.callbackSuccess` call fails with the guard panic and leaves state
  unchanged, while genuine cross-account-child → self callbacks retain successful decode and
  failed/oversized fallback behavior.

## Next

Keep general lifecycle policy separate: default non-payable, reusable private/init entry metadata,
and `STATE` migration belong to N9. Within Promises, parallel `promise_and` and native transfer
actions are the next independent Runtime/SDK slices.
