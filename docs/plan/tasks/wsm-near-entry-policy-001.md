# wsm-near-entry-policy-001 — NEAR private/payable entry metadata

Status: done

Depends on: [wsm-near-payable-001](wsm-near-payable-001.md),
[wsm-near-promise-private-001](wsm-near-promise-private-001.md)

## Scope

Add a target-owned generated-wrapper policy without introducing executable source operations:

- `@[pf_near_private]` and `@[pf_near_payable]` become opaque extractor annotations and are decoded
  only by NEAR IR; foreign targets fail closed rather than discarding them;
- canonical private/payable policy participates in the target digest, while empty policy preserves
  every existing foreign-target and unannotated NEAR digest;
- private wrappers compare exact predecessor/current AccountId length and all eight zero-padded
  words, then panic with `Method <name> is private` on mismatch;
- wrapper order is private, non-payable, arena/input decoding, lifecycle/state, then source body;
- explicit payable permits mutating donation-only methods, while attached-deposit observation
  remains payable for source compatibility and payable views are rejected;
- four `NearPromise` callbacks move from body-authentication branches to generated private policy.

## Verification

- `Tests.NearPromiseSpec` pins source annotations, canonical IR, malformed/foreign-policy rejection,
  payable-view rejection, legal private views, full AccountId comparison, exact wrapper ordering,
  callback-result domination, and absence of a deposit guard from donation-only `recordValue`.
- `runtime-tests/near/promise.sh` sends a paid external callback and observes the exact private panic
  before non-payable, then executes a paid body-independent method and retains all genuine callback
  success/failure/oversized/join scenes.
- The registered `NearPromise` WAT assembles through the locked toolchain and the full NEAR artifact
  gate checks every registered module.

## Next

Completed by [wsm-near-uninitialized-001](wsm-near-uninitialized-001.md): all ordinary
state-consuming entries now require the canonical `STATE` marker. Version/migration metadata
remains separate from broader callback codecs and arbitrary Promise handles.
