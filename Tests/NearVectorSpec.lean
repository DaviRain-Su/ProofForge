import Examples.NearVector
import Lean
import ProofForge

/-! Bounded direct-write NEAR Vector layout, extraction, and WAT invariants. -/

namespace Tests.NearVectorSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard Prefix4.wellFormed 0xffffffff
#guard !Prefix4.wellFormed 0x100000000
#guard DirectVector64.wellFormed 1
#guard DirectVector64.wellFormed 64
#guard !DirectVector64.wellFormed 0
#guard !DirectVector64.wellFormed 65
#guard (4 : DirectVector64).validLength 4
#guard !(4 : DirectVector64).validLength 5
#guard (4 : DirectVector64).contains 4 3
#guard !(4 : DirectVector64).contains 4 4
#guard (4 : DirectVector64).canPush 3
#guard !(4 : DirectVector64).canPush 4

private def key3 : ProofForge.Core.Value.BoundedBytes 8 :=
  (4 : DirectVector64).elementKey (0x31434556 : Prefix4) 3

#guard key3.length == 8
#guard key3.values[0] == 0x56
#guard key3.values[1] == 0x45
#guard key3.values[2] == 0x43
#guard key3.values[3] == 0x31
#guard key3.values[4] == 3
#guard key3.values[5] == 0
#guard key3.values[6] == 0
#guard key3.values[7] == 0

private def value : ProofForge.Core.Value.BoundedBytes 8 :=
  (4 : DirectVector64).elementValue 0x0102030405060708

#guard value.length == 8
#guard value.values[0] == 0x08
#guard value.values[1] == 0x07
#guard value.values[2] == 0x06
#guard value.values[3] == 0x05
#guard value.values[4] == 0x04
#guard value.values[5] == 0x03
#guard value.values[6] == 0x02
#guard value.values[7] == 0x01

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key val _ _)) => #[s!"write.{result}.{key}.{val}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

private partial def hasSourceLocal : Array ProofForge.Extract.IR.Op → Bool
  | ops => ops.any fun op =>
      match op with
      | .letLocal .. | .joinLocal .. | .setLocal .. => true
      | .ite _ _ _ thn els => hasSourceLocal thn || hasSourceLocal els
      | .forBody _ body => hasSourceLocal body
      | _ => false

elab "#pf_near_vector_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearVector with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "push" == #["write.8.8.8"] &&
      methodSteps "setFirst" == #["write.8.8.8"] &&
      methodSteps "pop" == #["remove.8.8"] &&
      methodSteps "getAt" == #["read.8.8"] do
    throwError s!"direct Vector storage effects were lost or reordered: " ++
      s!"push={methodSteps "push"}, set={methodSteps "setFirst"}, " ++
      s!"pop={methodSteps "pop"}, get={methodSteps "getAt"}"
  let some pushSource := source.methods.find? (·.ixName == "push")
    | throwError "missing NearVector.push"
  unless hasSourceLocal pushSource.ops do
    throwError "push no longer snapshots a scalar across its raw-storage effect"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func (export \"push\")",
    "(func (export \"setFirst\")",
    "(func (export \"pop\")",
    "(func (export \"getAt\")",
    "(local $pf_v0 i64)",
    "(call $pf_storage_write",
    "(call $pf_storage_remove",
    "(call $pf_storage_read",
    "i64.and",
    "i64.shr_u",
    "i64.shl",
    "i64.or",
    "(i64.const 826492246)",
    "(i64.const 8)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR DirectVector64 WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-vector: digest = {IR.digestHex program}"

#pf_near_vector_check

end Tests.NearVectorSpec
