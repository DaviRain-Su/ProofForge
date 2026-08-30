# wsm-near-init-001 — NEAR one-time initialization guard

Status: done

Depends on: [wsm-near-storage-001](wsm-near-storage-001.md)

## Scope

Give the generated NEAR `initialize` wrapper one-time lifecycle semantics:

- decode and validate entry input before consulting state, matching the current near-sdk-rs wrapper
  order;
- reserve the default near-sdk key `STATE`, reject a second initializer call with the exact
  `The contract has already been initialized` panic, and write the marker only after successful
  scalar-state persistence;
- also treat any existing canonical scalar field key as initialized, so contracts deployed with
  ProofForge's pre-marker layout cannot be reinitialized after a code upgrade;
- fail closed on partial legacy state and leave ordinary entries unable to write the marker.

The marker value is one internal byte whose contents are not a public codec. Contract state remains
independent 8-byte field values rather than near-sdk-rs's Borsh value under `STATE`; this slice does
not claim Rust layout compatibility, state versioning, migration, `ignore_state`, or rejection of
ordinary entries before initialization. Raw-storage and collection users must not claim the exact
reserved `STATE` key.

## Verification

- `Tests.NearSpec` pins the marker and exact panic data, argument/marker/legacy-slot check order,
  state-before-marker persistence, one marker write, and absence of marker writes from entries.
- The initializer emitter rejects a scalar-return terminal rather than silently bypassing marker
  persistence.
- `runtime-tests/near/counter.sh` calls `initialize` twice on near-sandbox 2.13.0 and verifies that
  the second receipt fails without changing the first initialized value.

## Next

Generated non-payable/private/payable metadata is complete in
[wsm-near-entry-policy-001](wsm-near-entry-policy-001.md), and ordinary missing-state behavior is
complete in [wsm-near-uninitialized-001](wsm-near-uninitialized-001.md). Versioned migration
remains a separate lifecycle cut.
