# wsm-near-state-envelope-001 — NEAR versioned STATE schema envelope

Status: done

Depends on: [wsm-near-uninitialized-001](wsm-near-uninitialized-001.md)

## Scope

Replace the existence-only marker with exact ProofForge-owned state metadata:

- `STATE` is 16 bytes: ASCII `PFNRST01` followed by the UInt64 schema digest in little-endian;
- the schema canonical form is domain-separated `near-state-schema-v1`, then the ordered slot count
  and length-delimited slot name, physical width, and ABI spelling;
- FNV-1a-64 is explicitly pinned as a compact engineering mismatch detector. It is not a
  collision-resistant commitment;
- program name, methods, entry policies, and executable operations are absent, so logic-only
  upgrades preserve compatibility while any ordered physical slot schema change fails closed;
- initialization stages the exact envelope at `[192, 208)` and writes it only after scalar state;
- every ordinary entry reads `STATE` into dedicated register 5, branches on missing status before
  consulting the register, then validates exact length, magic/version, and schema digest before any
  scalar or callback-result read;
- malformed, legacy one-byte, or foreign-schema envelopes panic with exact
  `The contract state version is incompatible`.

This does not claim near-sdk-rs Borsh `STATE` compatibility. Official near-sdk migrations are
manual authenticated transforms, commonly `#[private] #[init(ignore_state)]`; ProofForge's
split-key layout instead needs version-specific key readers and must advance this envelope last.
That migration entry remains a separate slice. Existing one-byte ProofForge markers deliberately
fail closed until migrated.

## Verification

- `Tests.NearSpec` pins the Counter canonical schema and FNV vector, method-only stability,
  name-change mismatch, exact scratch stores, write-last ordering, dedicated-register status/length
  discipline, magic/schema checks, and both lifecycle panics.
- `Tests.NearPromiseSpec` retains envelope validation before dependency-result reads.
- `runtime-tests/near/counter.sh` observes exact raw bytes
  `50464e5253543031ad143be1f1fee08d` and retains all lifecycle/arithmetic scenes.

## Next

Add one private migration entry policy with explicit old-envelope dispatch, per-key conversion, and
the invariant transformed state first → new envelope last. Do not add an unauthenticated
`ignore_state` equivalent.
