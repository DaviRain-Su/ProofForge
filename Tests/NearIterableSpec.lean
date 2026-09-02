import Examples.Near.NearIterable
import Lean
import ProofForge

/-! Bounded Identity IterableMap/IterableSet layout, extraction, and WAT invariants. -/

namespace Tests.NearIterableSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard Prefix3.wellFormed 0xffffff
#guard !Prefix3.wellFormed 0x1000000
#guard (0x504d49 : Prefix3).vectorTag == 0x76504d49
#guard (0x504d49 : Prefix3).lookupTag == 0x6d504d49
#guard DirectIterableMap64.wellFormed 1
#guard DirectIterableMap64.wellFormed 64
#guard !DirectIterableMap64.wellFormed 0
#guard !DirectIterableMap64.wellFormed 65
#guard (3 : DirectIterableMap64).validLength 3
#guard !(3 : DirectIterableMap64).validLength 4
#guard (3 : DirectIterableMap64).canInsert 2
#guard !(3 : DirectIterableMap64).canInsert 3
#guard (3 : DirectIterableSet64).containsIndex 3 2
#guard !(3 : DirectIterableSet64).containsIndex 3 3

private def vectorKey : ProofForge.Core.Value.BoundedBytes 8 :=
  (3 : DirectIterableMap64).vectorKey ((0x504d49 : Prefix3).vectorTag) 2

#guard vectorKey.length == 8
#guard vectorKey.values[0] == 0x49
#guard vectorKey.values[1] == 0x4d
#guard vectorKey.values[2] == 0x50
#guard vectorKey.values[3] == 0x76
#guard vectorKey.values[4] == 2
#guard vectorKey.values[5] == 0
#guard vectorKey.values[6] == 0
#guard vectorKey.values[7] == 0

private def lookupKey : ProofForge.Core.Value.BoundedBytes 12 :=
  (3 : DirectIterableMap64).lookupKey
    ((0x504d49 : Prefix3).lookupTag) 0x0102030405060708

#guard lookupKey.length == 12
#guard lookupKey.values[0] == 0x49
#guard lookupKey.values[1] == 0x4d
#guard lookupKey.values[2] == 0x50
#guard lookupKey.values[3] == 0x6d
#guard lookupKey.values[4] == 0x08
#guard lookupKey.values[11] == 0x01

private def mapValue : ProofForge.Core.Value.BoundedBytes 12 :=
  (3 : DirectIterableMap64).lookupValue 0x0102030405060708 2

#guard mapValue.length == 12
#guard mapValue.values[0] == 0x08
#guard mapValue.values[7] == 0x01
#guard mapValue.values[8] == 2
#guard mapValue.values[11] == 0

private def setValue : ProofForge.Core.Value.BoundedBytes 4 :=
  (3 : DirectIterableSet64).lookupValue 2

#guard setValue.length == 4
#guard setValue.values[0] == 2
#guard setValue.values[3] == 0

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

private partial def localCount : Array ProofForge.Extract.IR.Op → Nat
  | ops => ops.foldl (init := 0) fun count op =>
      count + match op with
      | .letLocal .. => 1
      | .ite _ _ _ thn els => localCount thn + localCount els
      | .forBody _ body => localCount body
      | _ => 0

elab "#pf_near_iterable_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearIterable with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "mapGet" == #["read.12.12"] &&
      methodSteps "mapIndex" == #["read.12.12"] &&
      methodSteps "mapKeyAt" == #["read.8.8"] &&
      methodSteps "mapHasKeyAt" == #["has.8.8"] &&
      methodSteps "mapPut" ==
        #["read.12.12", "write.8.8.8", "write.12.12.12", "write.12.12.12"] &&
      methodSteps "mapRemove" ==
        #["read.12.12", "remove.12.12", "remove.8.8", "read.8.8", "read.12.12",
          "remove.12.12", "write.8.8.8", "write.12.12.12", "remove.8.8"] &&
      methodSteps "setIndex" == #["read.4.12"] &&
      methodSteps "setKeyAt" == #["read.8.8"] &&
      methodSteps "setHasKeyAt" == #["has.8.8"] &&
      methodSteps "setInsert" == #["read.4.12", "write.8.8.8", "write.4.12.4"] &&
      methodSteps "setRemove" ==
        #["read.4.12", "remove.4.12", "remove.8.8", "read.8.8", "read.4.12",
          "remove.4.12", "write.8.8.8", "write.4.12.4", "remove.8.8"] do
    throwError "direct iterable storage effects were lost or reordered"
  let some mapRemoveSource := source.methods.find? (·.ixName == "mapRemove")
    | throwError "missing NearIterable.mapRemove"
  let some setRemoveSource := source.methods.find? (·.ixName == "setRemove")
    | throwError "missing NearIterable.setRemove"
  unless 3 ≤ localCount mapRemoveSource.ops && 2 ≤ localCount setRemoveSource.ops do
    throwError "swap-remove no longer snapshots mutable storage-result scalars across effects"
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
    "(func (export \"mapPut\")",
    "(func (export \"mapRemove\")",
    "(func (export \"setInsert\")",
    "(func (export \"setRemove\")",
    "(call $pf_storage_has_key",
    "(call $pf_storage_read",
    "(call $pf_storage_write",
    "(call $pf_storage_remove",
    "(i64.const 12)",
    "(i64.const 8)",
    "(i64.const 4)",
    "i64.lt_u",
    "i64.shl",
    "i64.or"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR direct iterable WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-iterable: digest = {IR.digestHex program}"

#pf_near_iterable_check

end Tests.NearIterableSpec
