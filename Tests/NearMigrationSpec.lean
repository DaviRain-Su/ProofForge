import Examples.Near.NearMigration
import Lean
import ProofForge

/-! Authenticated old-schema dispatch and write-last NEAR migration invariants. -/

namespace Tests.NearMigrationSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private def methodBody (wat method : String) : Except String String :=
  match wat.splitOn ("(func (export \"" ++ method ++ "\")") with
  | [_prefix, suffix] => pure ((suffix.splitOn "\n  (func (export").headD "")
  | _ => throw s!"expected exactly one {method} wrapper"

elab "#pf_near_migration_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearMigration with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceMigration := source.methods.find? (·.ixName == "migrate")
    | throwError "missing source migration entry"
  unless sourceMigration.annotations ==
      #["near.private.v1", "near.migrate.v1:10223451468950344877"] do
    throwError s!"migration source annotations changed: {sourceMigration.annotations}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some migration := program.entries.find? (·.ixName == "migrate")
    | throwError "missing lowered migration entry"
  let migrationPolicy ←
    match IR.entryPolicyOf migration with
    | .ok policy => pure policy
    | .error reason => throwError reason
  unless migrationPolicy.isPrivate && !migrationPolicy.payable &&
      migrationPolicy.migrateFrom == some (0x8de0fef1e13b14ad : UInt64) &&
      migration.entryPolicy ==
        "near.entry.v2:private,migrate-from:10223451468950344877" do
    throwError s!"wrong migration target policy: {repr migrationPolicy}"
  unless IR.stateSchemaCanonical program ==
      "near-state-schema-v1|2|5:total:8:6:u64-le/8:revision:8:6:u64-le" &&
      IR.stateSchemaDigest program == (0x9b8fca21d3d2fcee : UInt64) do
    throwError s!"wrong migration target schema: {IR.stateSchemaCanonical program}"
  for malformed in #[
      "near.entry.v2:private,migrate-from:010223451468950344877",
      "near.entry.v2:private,migrate-from:18446744073709551616",
      "near.entry.v2:migrate-from:10223451468950344877"] do
    match IR.EntryPolicy.ofCanonical malformed with
    | .error _ => pure ()
    | .ok _ => throwError s!"accepted malformed migration policy {malformed}"
  let noPrivate := { source with methods := source.methods.map fun method =>
    if method.ixName == "migrate" then
      { method with annotations := #["near.migrate.v1:10223451468950344877"] }
    else method }
  match IR.fromExtracted noPrivate with
  | .error reason =>
      unless reason.contains "migration requires pf_near_private" do
        throwError s!"wrong unauthenticated migration rejection: {reason}"
  | .ok _ => throwError "accepted unauthenticated migration"
  let payable := { source with methods := source.methods.map fun method =>
    if method.ixName == "migrate" then
      { method with annotations := method.annotations.push "near.payable.v1" }
    else method }
  match IR.fromExtracted payable with
  | .error reason =>
      unless reason.contains "migration cannot be payable" do
        throwError s!"wrong payable migration rejection: {reason}"
  | .ok _ => throwError "accepted payable migration"
  let sameSchema := { program with entries := program.entries.map fun method =>
    if method.ixName == "migrate" then
      { method with entryPolicy :=
          ({ isPrivate := true, migrateFrom := some (IR.stateSchemaDigest program) } :
            IR.EntryPolicy).canonical }
    else method }
  match Emit.emit sameSchema with
  | .error reason =>
      unless reason.contains "migration source schema equals current schema" do
        throwError s!"wrong no-op schema migration rejection: {reason}"
  | .ok _ => throwError "accepted migration from the current schema"
  let stateReading := { program with entries := program.entries.map fun method =>
    if method.ixName == "migrate" then
      { method with ops := #[.returnState (.field (.arg 0) "total")] }
    else method }
  match Emit.emit stateReading with
  | .error reason =>
      unless reason.contains "migration must read old state through explicit storage keys" do
        throwError s!"wrong implicit-state migration rejection: {reason}"
  | .ok _ => throwError "accepted migration that reads current-schema state"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let migrateBody ←
    match methodBody wat "migrate" with
    | .ok body => pure body
    | .error reason => throwError reason
  let privateAnchor := "(call $pf_predecessor_account_id"
  let depositAnchor := "(call $pf_attached_deposit (i64.const 24))"
  let oldDigestAnchor := "(i64.const 10223451468950344877)"
  let rawReadAnchor := "(global.set $pf_storage_result_status (call $pf_storage_read"
  let totalWrite :=
    "(call $pf_storage_write (i64.const 5) (i64.const 1024) (i64.const 8)"
  let revisionWrite :=
    "(call $pf_storage_write (i64.const 8) (i64.const 1029) (i64.const 8)"
  let envelopeWrite :=
    "(call $pf_storage_write (i64.const 5) (i64.const 2096) (i64.const 16)"
  let afterPrivate ← match migrateBody.splitOn privateAnchor with
    | [before, after] =>
        unless !before.contains depositAnchor do
          throwError "migration checked deposit before private authentication"
        pure after
    | _ => throwError "migration must authenticate predecessor exactly once"
  let afterDeposit ← match afterPrivate.splitOn depositAnchor with
    | [before, after] =>
        unless !before.contains oldDigestAnchor do
          throwError "migration checked its old schema before non-payable policy"
        pure after
    | _ => throwError "migration must enforce non-payable exactly once"
  let afterOldDigest ← match afterDeposit.splitOn oldDigestAnchor with
    | [before, after] =>
        unless before.contains
            "(call $pf_storage_read (i64.const 5) (i64.const 2096) (i64.const 5))" &&
            before.contains "(call $pf_register_len (i64.const 5))" &&
            before.contains "(i64.load (i32.const 192))" do
          throwError "migration lost exact old-envelope status/length/magic checks"
        pure after
    | _ => throwError "migration must dispatch one exact old schema digest"
  let afterRawRead ← match afterOldDigest.splitOn rawReadAnchor with
    | [before, after] =>
        unless !before.contains totalWrite && !before.contains revisionWrite do
          throwError "migration wrote transformed fields before reading the old key"
        pure after
    | _ => throwError "migration must read its old value through bounded raw storage"
  let afterTotal ← match afterRawRead.splitOn totalWrite with
    | [before, after] =>
        unless (before.splitOn "(call $pf_storage_result_byte").length == 9 do
          throwError "migration wrote transformed state before validating its old value"
        pure after
    | _ => throwError "migration must write total exactly once"
  let afterRevision ← match afterTotal.splitOn revisionWrite with
    | [_before, after] => pure after
    | _ => throwError "migration must write revision exactly once"
  match afterRevision.splitOn envelopeWrite with
  | [before, _after] =>
      unless before.contains
          "(i64.store (i32.const 200) (i64.const 11209400244185005294))" do
        throwError "migration did not stage the current schema after transformed fields"
  | _ => throwError "migration must advance the current envelope exactly once and last"
  unless !migrateBody.contains
        "(call $pf_storage_read (i64.const 5) (i64.const 1024) (i64.const 1))" &&
      !migrateBody.contains
        "(call $pf_storage_read (i64.const 8) (i64.const 1029) (i64.const 1))" do
    throwError "migration implicitly loaded current-schema scalar slots"
  unless (wat.splitOn envelopeWrite).length == 3 do
    throwError "only initializer and migration may write the STATE envelope"
  logInfo m!"proofforge-near-migration: digest = {IR.digestHex program}"

#pf_near_migration_check

end Tests.NearMigrationSpec
