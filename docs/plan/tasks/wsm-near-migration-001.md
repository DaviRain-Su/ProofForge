# wsm-near-migration-001 — authenticated NEAR state migration

Status: done

Depends on: [wsm-near-state-envelope-001](wsm-near-state-envelope-001.md),
[wsm-near-storage-001](wsm-near-storage-001.md),
[wsm-near-entry-policy-001](wsm-near-entry-policy-001.md)

## Scope

Add one explicit upgrade path for ProofForge's split-key state:

- `@[pf_near_migrate OLD_SCHEMA_DIGEST]` is target-owned metadata, not a source operation;
- migration must also carry explicit `@[pf_near_private]`, must be a zero-argument non-payable
  mutator, and at most one migration entry may exist in a program;
- the declared old digest must differ from the current ordered slot schema digest;
- the generated wrapper keeps private → non-payable → input/prelude order, then validates exact
  `PFNRST01 || OLD_SCHEMA_DIGEST_le`; missing state keeps the uninitialized panic and any malformed,
  foreign, current, or already-migrated envelope keeps the incompatible-state panic;
- migration source code may not read or forward its current `State` argument. It must decode prior
  values through explicit bounded raw-storage keys, so the wrapper never loads current-schema
  scalar slots before conversion;
- successful source-emitted current field writes happen before the emitter stages and writes the
  current schema envelope. Error/trap paths do not advance the envelope, and NEAR transaction
  rollback remains authoritative;
- prior split keys are retained unless migration source code explicitly removes them. No automatic
  garbage collection or general near-sdk-rs Borsh `STATE` compatibility is claimed.

The `NearMigration` fixture migrates the one-field Counter schema (`value`) into `total` plus
`revision`, decoding the exact old `value` key as UInt64 LE and retaining that legacy key.

## Verification

- `Tests.NearMigrationSpec` pins annotation/canonical parsing, exact old/current digest vectors,
  rejection of unauthenticated/payable/current-schema/implicit-state migrations, wrapper order,
  dedicated envelope-register checks, absence of current-slot loads, explicit old-key read, and
  transformed fields → current envelope ordering.
- `runtime-tests/near/check.sh` assembles and checks the registered migration fixture.
- `runtime-tests/near/counter.sh` deploys Counter V1, initializes and mutates it, upgrades code to
  the two-field fixture, observes ordinary-entry incompatibility, rejects an external migration at
  the private guard, performs same-account migration, checks exact new raw keys/envelope, rejects
  repeated migration, and executes a post-migration mutation on near-sandbox 2.13.0.

## Next

Return to the SDK/runtime roadmap: broaden collection metadata and codec surfaces only where a
concrete complex-contract fixture needs them. Dynamic Promise handles/arbitrary joins and nested
Borsh/JSON remain independent slices.
