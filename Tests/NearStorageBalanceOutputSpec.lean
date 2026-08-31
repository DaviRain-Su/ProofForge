import Examples.NearStorageBalanceOutput
import Lean
import ProofForge

/-! Exact compiler-owned `Option<StorageBalance>` JSON output planning and WAT checks. -/

namespace Tests.NearStorageBalanceOutputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private def ordinarySchema : ProofForge.Core.Codec.Schema :=
  .record "Tests.NearStorageBalanceOutputSpec.Ordinary" #[
    ("registered", .scalar .uint64), ("total", .scalar .uint128),
    ("available", .scalar .uint128)]

#guard Codec.storageBalanceResultSchema ==
  .record "ProofForge.Wasm.Near.Runtime.StorageBalanceResult" #[
    ("registered", .scalar .uint64), ("total", .scalar .uint128),
    ("available", .scalar .uint128)]
#guard match Codec.targetOutputPlan Codec.storageBalanceResultSchema with
  | .ok .jsonStorageBalanceOption => true
  | _ => false
#guard match Codec.targetOutputPlan ordinarySchema with
  | .error _ => true
  | .ok _ => false

private def returnCount (method : IR.Method) : Nat :=
  method.ops.foldl (init := 0) fun count op =>
    match op with
    | .returnU64 _ => count + 1
    | _ => count

elab "#pf_near_storage_balance_output_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearStorageBalanceOutput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceAsymmetric := source.methods.find? (·.ixName == "someAsymmetric")
    | throwError "missing source someAsymmetric"
  unless sourceAsymmetric.retSchema == Codec.storageBalanceResultSchema &&
      sourceAsymmetric.retCount == 5 do
    throwError "extractor did not retain the exact five-leaf StorageBalance frame"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some asymmetric := program.entries.find? (·.ixName == "someAsymmetric")
    | throwError "missing target someAsymmetric"
  unless asymmetric.outputSchema == some Codec.storageBalanceResultSchema &&
      asymmetric.outputPolicy == "near-json-storage-balance-option-v1" &&
      asymmetric.tupleArity == some 5 && returnCount asymmetric == 5 do
    throwError "target lost the exact StorageBalance schema, frame, or output policy"
  let malformedCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "someAsymmetric" then { method with retCount := 4 } else method }
  match IR.fromExtracted malformedCount with
  | .error reason =>
      unless reason.contains "output frame does not match its StorageBalance plan" do
        throwError s!"wrong malformed StorageBalance frame rejection: {reason}"
  | .ok _ => throwError "malformed StorageBalance frame was accepted"
  let mutating := { source with methods := source.methods.map fun method =>
    if method.ixName == "someAsymmetric" then { method with kind := .increment } else method }
  match IR.fromExtracted mutating with
  | .error reason =>
      unless reason.contains "StorageBalance output currently requires a view" do
        throwError s!"wrong mutating StorageBalance rejection: {reason}"
  | .ok _ => throwError "mutating StorageBalance output was accepted"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func $pf_u128_decimal",
    "(local $pf_output_second_length i64)",
    "(if (i64.gt_u (i64.const 1) (i64.const 1)) (then unreachable))",
    "(call $pf_arena_alloc (i64.const 4) (i64.const 1))",
    "(i32.const 1819047278)",
    "(call $pf_arena_alloc (i64.const 105) (i64.const 1))",
    "(i64.const 2480464647488283259)",
    "(i64.const 7811882189714500642)",
    "(i64.const 9634068613063265)",
    "(i64.const 32034)",
    "(i64.const 27)) (i64.extend_i32_u (local.get $pf_output_ptr)))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"StorageBalance output WAT missing {anchor}"
  if wat.contains "(func $pf_json_escape_byte" then
    throwError "StorageBalance numeric output pulled in the unrelated JSON string escaper"
  unless (wat.splitOn "(func $pf_u128_decimal").length == 2 do
    throwError "StorageBalance output did not include exactly one shared decimal helper"
  let parts := wat.splitOn "(func (export \"someAsymmetric\")"
  unless parts.length == 2 do
    throwError "missing unique someAsymmetric export body"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  unless (body.splitOn "(call $pf_u128_decimal").length == 3 do
    throwError "StorageBalance Some branch must render exactly two independent u128 values"
  unless (body.splitOn "(call $pf_value_return").length == 3 do
    throwError "StorageBalance terminal must have one mutually exclusive return per runtime branch"
  let mismatchedPolicy := { program with entries := program.entries.map fun method =>
    if method.ixName == "someAsymmetric" then
      { method with outputPolicy := "wrong" }
    else method }
  match Emit.emit mismatchedPolicy with
  | .error reason =>
      unless reason.contains "output policy does not match" do
        throwError s!"wrong output-policy rejection: {reason}"
  | .ok _ => throwError "mismatched StorageBalance output policy was accepted"
  logInfo m!"proofforge-near-storage-balance-output: digest = {IR.digestHex program}"

#pf_near_storage_balance_output_check

end Tests.NearStorageBalanceOutputSpec
