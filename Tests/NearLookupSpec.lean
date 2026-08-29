import Examples.NearLookup
import Lean
import ProofForge

/-! Direct Identity LookupMap/LookupSet layout, extraction, and WAT invariants. -/

namespace Tests.NearLookupSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard DirectLookupMap64.wellFormed 0x3150414d
#guard DirectLookupSet64.wellFormed 0x31544553
#guard !DirectLookupMap64.wellFormed 0x100000000

private def mapKey : ProofForge.Core.Value.BoundedBytes 12 :=
  (0x3150414d : DirectLookupMap64).elementKey 0x0102030405060708

#guard mapKey.length == 12
#guard mapKey.values[0] == 0x4d
#guard mapKey.values[1] == 0x41
#guard mapKey.values[2] == 0x50
#guard mapKey.values[3] == 0x31
#guard mapKey.values[4] == 0x08
#guard mapKey.values[5] == 0x07
#guard mapKey.values[6] == 0x06
#guard mapKey.values[7] == 0x05
#guard mapKey.values[8] == 0x04
#guard mapKey.values[9] == 0x03
#guard mapKey.values[10] == 0x02
#guard mapKey.values[11] == 0x01

private def mapValue : ProofForge.Core.Value.BoundedBytes 8 :=
  (0x3150414d : DirectLookupMap64).elementValue 0x8877665544332211

#guard mapValue.length == 8
#guard mapValue.values[0] == 0x11
#guard mapValue.values[7] == 0x88

private def setValue : ProofForge.Core.Value.BoundedBytes 1 :=
  (0x31544553 : DirectLookupSet64).elementValue

#guard setValue.length == 0

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key value _ _)) =>
          #[s!"write.{result}.{key}.{value}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ext (.near (.storageHasKey result key _)) => #[s!"has.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

elab "#pf_near_lookup_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearLookup with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "mapGet" == #["read.8.12"] &&
      methodSteps "mapHas" == #["has.8.12"] &&
      methodSteps "mapPut" == #["write.8.12.8"] &&
      methodSteps "mapRemove" == #["remove.8.12"] &&
      methodSteps "setHas" == #["has.1.12"] &&
      methodSteps "setInsert" == #["write.1.12.1"] &&
      methodSteps "setRemove" == #["remove.1.12"] do
    throwError s!"direct lookup storage effects were lost or reordered: " ++
      s!"get={methodSteps "mapGet"}, has={methodSteps "mapHas"}, " ++
      s!"put={methodSteps "mapPut"}, remove={methodSteps "mapRemove"}, " ++
      s!"setHas={methodSteps "setHas"}, setInsert={methodSteps "setInsert"}, " ++
      s!"setRemove={methodSteps "setRemove"}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  for method in program.entries do
    match Emit.emit { program with entries := #[method] } with
    | .ok _ => pure ()
    | .error reason => throwError s!"{method.ixName}: {reason}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func (export \"mapGet\")",
    "(func (export \"mapPut\")",
    "(func (export \"mapRemove\")",
    "(func (export \"setInsert\")",
    "(func (export \"setRemove\")",
    "(call $pf_storage_has_key",
    "(call $pf_storage_read",
    "(call $pf_storage_write",
    "(call $pf_storage_remove",
    "(i64.const 12)",
    "i64.and",
    "i64.shr_u",
    "i64.shl",
    "i64.or"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR direct lookup WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-lookup: digest = {IR.digestHex program}"

#pf_near_lookup_check

end Tests.NearLookupSpec
