import Examples.Near.NearQueue
import Lean
import ProofForge

/-! ProofForge bounded direct Queue layout, extraction, and WAT invariants. -/

namespace Tests.NearQueueSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard DirectQueue64.wellFormed 1
#guard DirectQueue64.wellFormed 64
#guard !DirectQueue64.wellFormed 0
#guard !DirectQueue64.wellFormed 65
#guard (3 : DirectQueue64).validState 0 0
#guard (3 : DirectQueue64).validState 2 3
#guard !(3 : DirectQueue64).validState 1 0
#guard !(3 : DirectQueue64).validState 3 1
#guard !(3 : DirectQueue64).validState 0 4
#guard (3 : DirectQueue64).canPush 2 2
#guard !(3 : DirectQueue64).canPush 2 3
#guard (3 : DirectQueue64).canPop 2 1
#guard !(3 : DirectQueue64).canPop 0 0
#guard (3 : DirectQueue64).offsetInRange 2 3 2
#guard !(3 : DirectQueue64).offsetInRange 2 3 3
#guard (3 : DirectQueue64).physicalIndex 0 0 == 0
#guard (3 : DirectQueue64).physicalIndex 2 0 == 2
#guard (3 : DirectQueue64).physicalIndex 2 1 == 0
#guard (3 : DirectQueue64).physicalIndex 2 2 == 1
#guard (3 : DirectQueue64).nextHead 0 == 1
#guard (3 : DirectQueue64).nextHead 2 == 0

private def wrappedKey : ProofForge.Core.Value.BoundedBytes 8 :=
  (3 : DirectQueue64).elementKey (0x31455551 : Prefix4)
    ((3 : DirectQueue64).physicalIndex 2 1)

#guard wrappedKey.length == 8
#guard wrappedKey.values[0] == 0x51
#guard wrappedKey.values[1] == 0x55
#guard wrappedKey.values[2] == 0x45
#guard wrappedKey.values[3] == 0x31
#guard wrappedKey.values[4] == 0
#guard wrappedKey.values[5] == 0
#guard wrappedKey.values[6] == 0
#guard wrappedKey.values[7] == 0

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

elab "#pf_near_queue_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearQueue with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "push" == #["write.8.8.8"] &&
      methodSteps "pop" == #["remove.8.8", "remove.8.8"] &&
      methodSteps "getAt" == #["read.8.8"] &&
      methodSteps "hasAt" == #["has.8.8"] &&
      methodSteps "peek" == #["read.8.8"] do
    throwError s!"direct Queue storage effects were lost or reordered: " ++
      s!"push={methodSteps "push"}, pop={methodSteps "pop"}, " ++
      s!"getAt={methodSteps "getAt"}, peek={methodSteps "peek"}"
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
    "(func (export \"push\")",
    "(func (export \"pop\")",
    "(func (export \"getAt\")",
    "(func (export \"hasAt\")",
    "(func (export \"peek\")",
    "(func (export \"getHead\")",
    "(call $pf_storage_has_key",
    "(call $pf_storage_read",
    "(call $pf_storage_write",
    "(call $pf_storage_remove",
    "(i64.const 3)",
    "(i64.const 826627409)",
    "i64.lt_u",
    "i64.sub"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR DirectQueue64 WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-queue: digest = {IR.digestHex program}"

#pf_near_queue_check

end Tests.NearQueueSpec
