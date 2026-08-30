# wsm-near-uninitialized-001 — NEAR fail-closed uninitialized entries

Status: done

Depends on: [wsm-near-entry-policy-001](wsm-near-entry-policy-001.md),
[wsm-near-init-001](wsm-near-init-001.md)

## Scope

Make ProofForge's explicit-initializer lifecycle fail closed:

- every ordinary state-consuming entry, including views and private callbacks, requires the exact
  reserved `STATE` marker before reading any scalar field;
- the generated guard runs after private, non-payable, input decoding, and required host prelude,
  but before field storage reads and the source body;
- a missing marker panics with exact `The contract is not initialized`, matching the behavior of
  current near-sdk-rs contracts that derive `PanicOnDefault`;
- the initializer keeps its separate post-input already-initialized/legacy-field guard and remains
  the only generated path that writes `STATE`;
- the shared panic bytes are emitted once in the bounded lifecycle-data region.

This is an explicit ProofForge policy, not a claim that near-sdk-rs always rejects missing state.
The official wrapper uses `ContractState::state_read().unwrap_or_default()`: ordinary `Default`
permits implicit first-use state, while `PanicOnDefault` produces the panic above. All current
ProofForge entries consume contract state and all current contracts provide an explicit initializer,
so the safer branch is canonical here. Input decoding still precedes the marker check, as in the
official wrapper; malformed pre-initialization input therefore reports the input failure first.

Legacy field-only deployments remain protected from reinitialization by the initializer's existing
field-key checks but cannot execute ordinary entries without a future explicit migration. A present
marker with missing/malformed scalar fields, marker versioning, and state migration remain separate
lifecycle work.

## Verification

- `Tests.NearSpec` pins one exact missing-marker existence check on every ordinary Counter wrapper,
  input-before-marker and marker-before-field-read order, no missing-marker branch on the
  initializer, exact deduplicated panic bytes, and field-before-marker initialization.
- `Tests.NearPromiseSpec` pins the marker check before callback dependency-result reads.
- `runtime-tests/near/counter.sh` proves paid pre-initialization mutation is rejected by non-payable
  first; zero-deposit mutation and a view then fail with the exact lifecycle panic without creating
  state; initialization and the existing repeated-init/arithmetic scenes still pass.

## Next

The versioned metadata is complete in
[wsm-near-state-envelope-001](wsm-near-state-envelope-001.md), and its explicit authenticated
split-key upgrade path is complete in [wsm-near-migration-001](wsm-near-migration-001.md). General
near-sdk-rs state serialization remains outside the boundary.
