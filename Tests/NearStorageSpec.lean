import Examples.Near.NearStorage
import Lean
import ProofForge

/-! Raw binary NEAR storage extraction, planning, and WAT invariants. -/

namespace Tests.NearStorageSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.storageCapacityValid 1
#guard Codec.storageCapacityValid 64
#guard !Codec.storageCapacityValid 0
#guard !Codec.storageCapacityValid 65
#guard Codec.rawStorageKeyCapacityValid 65
#guard Codec.rawStorageKeyCapacityValid 72
#guard !Codec.rawStorageKeyCapacityValid 0
#guard !Codec.rawStorageKeyCapacityValid 73
#guard ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.wellFormed 8
#guard !ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.wellFormed 65
#guard match Codec.inputPlan (.boundedBytes 65) with | .error _ => true | .ok _ => false
#guard match Codec.outputPlan (.boundedBytes 65) with | .error _ => true | .ok _ => false

private def extractStorageStep : ProofForge.Extract.IR.Op → Option String
  | .ext (.near (.storageRead result key _)) => some s!"read.{result}.{key}"
  | .ext (.near (.storageWrite result key value _ _)) => some s!"write.{result}.{key}.{value}"
  | .ext (.near (.storageRemove result key _)) => some s!"remove.{result}.{key}"
  | .ext (.near (.storageHasKey result key _)) => some s!"has.{result}.{key}"
  | _ => none

private def storageStep : ProofForge.Wasm.Near.IR.Method → Array String
  | method => method.ops.filterMap fun
      | .ext (.storageRead result key _) => some s!"read.{result}.{key}"
      | .ext (.storageWrite result key value _ _) => some s!"write.{result}.{key}.{value}"
      | .ext (.storageRemove result key _) => some s!"remove.{result}.{key}"
      | .ext (.storageHasKey result key _) => some s!"has.{result}.{key}"
      | _ => none

elab "#pf_near_storage_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearStorage with
    | .ok program => pure program
    | .error reason => throwError reason
  let sourceSteps := source.methods.foldl (init := #[]) fun steps method =>
    steps ++ method.ops.filterMap extractStorageStep
  unless sourceSteps.contains "write.8.4.8" && sourceSteps.contains "read.8.4" &&
      sourceSteps.contains "read.8.2" &&
      sourceSteps.contains "read.4.4" && sourceSteps.contains "remove.8.4" &&
      sourceSteps.contains "has.8.4" && sourceSteps.contains "write.8.1.8" &&
      sourceSteps.contains "has.8.1" && sourceSteps.contains "write.8.72.8" &&
      sourceSteps.contains "read.8.72" && sourceSteps.contains "remove.8.72" &&
      sourceSteps.contains "has.8.72" do
    throwError s!"extractor lost raw storage effects: {repr sourceSteps}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some put := program.entries.find? (·.ixName == "put")
    | throwError "missing NearStorage.put"
  let some readByte := program.entries.find? (·.ixName == "readByte")
    | throwError "missing NearStorage.readByte"
  unless storageStep put == #["write.8.4.8"] && storageStep readByte == #["read.8.4"] &&
      put.inputSchema == some (.boundedBytes 8) do
    throwError s!"wrong raw storage target lowering: put={repr (storageStep put)}, " ++
      s!"readByte={repr (storageStep readByte)}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"storage_remove\"",
    "(import \"env\" \"storage_has_key\"",
    "(global $pf_storage_result_status (mut i64)",
    "(func $pf_storage_result_byte",
    "(call $pf_storage_write",
    "(call $pf_storage_read",
    "(call $pf_storage_remove",
    "(call $pf_storage_has_key",
    "(func (export \"putMaximumKey\")",
    "(func (export \"readMaximumKeyByte\")",
    "(func (export \"removeMaximumKey\")",
    "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
    "(func (export \"staleByteAfterMiss\")",
    "(i64.const 3)",
    "(if (i64.gt_u (global.get $pf_storage_result_status) (i64.const 1))",
    "(if (i64.eq (global.get $pf_storage_result_status) (i64.const 1))",
    "(global.set $pf_storage_result_length (call $pf_register_len (i64.const 3))",
    "(if (i64.gt_u (global.get $pf_storage_result_length) (i64.const 4))",
    "(call $pf_arena_alloc (global.get $pf_storage_result_length) (i64.const 1))",
    "(call $pf_read_register (i64.const 3)",
    "(i64.store8 (i32.add (i32.wrap_i64",
    "(if (i64.ne (call $pf_register_len (i64.const 1)) (i64.const 8))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR raw storage WAT missing {anchor}\n{wat}"
  let viewWrite := { source with methods := source.methods.map fun method =>
    if method.ixName == "put" then { method with kind := .get } else method }
  match IR.fromExtracted viewWrite >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot write raw storage" do
        throwError s!"wrong view-write rejection: {reason}"
  | .ok _ => throwError "raw storage write was accepted in a view"
  let viewRemove := { source with methods := source.methods.map fun method =>
    if method.ixName == "remove" then { method with kind := .get } else method }
  match IR.fromExtracted viewRemove >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot remove raw storage" do
        throwError s!"wrong view-remove rejection: {reason}"
  | .ok _ => throwError "raw storage remove was accepted in a view"
  logInfo m!"proofforge-near-storage: digest = {IR.digestHex program}"

#pf_near_storage_check

end Tests.NearStorageSpec
