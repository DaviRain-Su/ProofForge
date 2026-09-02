import Examples.Near.NearStorageBalanceBoundsOutput
import Lean
import ProofForge

/-! Exact compiler-owned `StorageBalanceBounds` JSON output planning and WAT checks. -/

namespace Tests.NearStorageBalanceBoundsOutputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private def ordinarySchema : ProofForge.Core.Codec.Schema :=
  .record "Tests.NearStorageBalanceBoundsOutputSpec.Ordinary" #[
    ("min", .scalar .uint128), ("hasMax", .scalar .uint64),
    ("max", .scalar .uint128)]

#guard Codec.storageBalanceBoundsResultSchema ==
  .record "ProofForge.Wasm.Near.Runtime.StorageBalanceBoundsResult" #[
    ("min", .scalar .uint128), ("hasMax", .scalar .uint64),
    ("max", .scalar .uint128)]
#guard match Codec.targetOutputPlan Codec.storageBalanceBoundsResultSchema with
  | .ok .jsonStorageBalanceBounds => true
  | _ => false
#guard match Codec.targetOutputPlan ordinarySchema with
  | .error _ => true
  | .ok _ => false

private def returnCount (method : IR.Method) : Nat :=
  method.ops.foldl (init := 0) fun count op =>
    match op with
    | .returnU64 _ => count + 1
    | _ => count

elab "#pf_near_storage_balance_bounds_output_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearStorageBalanceBoundsOutput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceAsymmetric := source.methods.find? (·.ixName == "someAsymmetric")
    | throwError "missing source someAsymmetric"
  unless sourceAsymmetric.retSchema == Codec.storageBalanceBoundsResultSchema &&
      sourceAsymmetric.retCount == 5 do
    throwError "extractor did not retain the exact five-leaf StorageBalanceBounds frame"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some asymmetric := program.entries.find? (·.ixName == "someAsymmetric")
    | throwError "missing target someAsymmetric"
  unless asymmetric.outputSchema == some Codec.storageBalanceBoundsResultSchema &&
      asymmetric.outputPolicy == "near-json-storage-balance-bounds-v1" &&
      asymmetric.tupleArity == some 5 && returnCount asymmetric == 5 do
    throwError "target lost the exact StorageBalanceBounds schema, frame, or output policy"
  let malformedCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "someAsymmetric" then { method with retCount := 4 } else method }
  match IR.fromExtracted malformedCount with
  | .error reason =>
      unless reason.contains "output frame does not match its StorageBalanceBounds plan" do
        throwError s!"wrong malformed StorageBalanceBounds frame rejection: {reason}"
  | .ok _ => throwError "malformed StorageBalanceBounds frame was accepted"
  let mutating := { source with methods := source.methods.map fun method =>
    if method.ixName == "someAsymmetric" then { method with kind := .increment } else method }
  match IR.fromExtracted mutating with
  | .error reason =>
      unless reason.contains "StorageBalanceBounds output currently requires a view" do
        throwError s!"wrong mutating StorageBalanceBounds rejection: {reason}"
  | .ok _ => throwError "mutating StorageBalanceBounds output was accepted"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func $pf_u128_decimal",
    "(local $pf_output_second_length i64)",
    "(call $pf_arena_alloc (i64.const 97) (i64.const 1))",
    "(i64.const 2466321603549274747)",
    "(i64.const 4189042963246099490)",
    "(i32.const 1819047278)",
    "(i64.const 32034)",
    "(i64.const 21)) (i64.extend_i32_u (local.get $pf_output_ptr)))",
    "(i64.const 19)) (i64.extend_i32_u (local.get $pf_output_ptr)))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"StorageBalanceBounds output WAT missing {anchor}"
  if wat.contains "(func $pf_json_escape_byte" then
    throwError "StorageBalanceBounds numeric output pulled in the unrelated JSON string escaper"
  unless (wat.splitOn "(func $pf_u128_decimal").length == 2 do
    throwError "StorageBalanceBounds output did not include exactly one shared decimal helper"
  let parts := wat.splitOn "(func (export \"someAsymmetric\")"
  unless parts.length == 2 do
    throwError "missing unique someAsymmetric export body"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  unless (body.splitOn "(call $pf_u128_decimal").length == 3 do
    throwError "StorageBalanceBounds Some branch must render two independent u128 values"
  unless (body.splitOn "(call $pf_value_return").length == 3 do
    throwError "StorageBalanceBounds terminal must return once in each mutually exclusive max branch"
  let mismatchedPolicy := { program with entries := program.entries.map fun method =>
    if method.ixName == "someAsymmetric" then { method with outputPolicy := "wrong" } else method }
  match Emit.emit mismatchedPolicy with
  | .error reason =>
      unless reason.contains "output policy does not match" do
        throwError s!"wrong output-policy rejection: {reason}"
  | .ok _ => throwError "mismatched StorageBalanceBounds output policy was accepted"
  logInfo m!"proofforge-near-storage-balance-bounds-output: digest = {IR.digestHex program}"

#pf_near_storage_balance_bounds_output_check

end Tests.NearStorageBalanceBoundsOutputSpec
