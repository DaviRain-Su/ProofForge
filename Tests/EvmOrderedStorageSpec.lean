import ProofForge
import Examples.EvmOrderedStorage

namespace Tests.EvmOrderedStorageSpec

open ProofForge.Evm
open ProofForge.Evm.Sdk
open Lean Elab Command

private def value : Ops.Val := .lit 7
private def call : StaticStorage.Call Ops.Val := .storeU64 "status" value

/-! ## Closed component contract -/

#guard call.values == #[value]
#guard call.effects.writesStorage
#guard call.wellFormed (fun operand => operand.wellFormed Ops.ValKind.arity)
#guard !(StaticStorage.Call.storeU64 "" value).wellFormed
  (fun operand => operand.wellFormed Ops.ValKind.arity)
#guard call.canonical (fun _ => "v") == "sstore.now.status(v)"
#guard
  (Component.Call.staticStorage call).effects ==
    ({ writesStorage := true } : Component.EffectSummary)

/-! ## Narrow schema resolver and byte-exact emission -/

private def emitContext : StaticStorage.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("  let v := 7\n", "v", st + 1)
    resolveU64Slot := fun field =>
      if field == "status" then .ok 4
      else .error s!"unknown {field}"
    indent := "  " }

#guard
  match StaticStorage.Emit.emitCall emitContext call 0 with
  | .ok (text, result, st) =>
      text == "  let v := 7\n  sstore(4, v)\n" && result == "v" && st == 1
  | .error _ => false

#guard
  match StaticStorage.Emit.emitCall emitContext (.storeU64 "missing" value) 0 with
  | .error reason => reason == "unknown missing"
  | .ok _ => false

/-! ## Source SDK host contract -/

private def statusHandle : Storage.Static.Handle UInt64 :=
  (Storage.Static.Layout.root.uint64 "status").handle

#guard statusHandle.storeNow 9 == 9
#guard Examples.EvmOrderedStorage.layout.wellFormed
#guard Examples.EvmOrderedStorage.layout.matchesFlattened [("status", 8)]

private partial def calls (ops : Array IR.Op) : Array (Component.Call Ops.Val) :=
  ops.foldl (init := #[]) fun acc op =>
    match op with
    | .component call => acc.push call
    | .ite _ _ _ thenOps elseOps => acc ++ calls thenOps ++ calls elseOps
    | .forBody _ body => acc ++ calls body
    | _ => acc

private def expectOrderedStorage : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmOrderedStorage with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless program.slots.toList.map (fun slot => (slot.name, slot.width)) == [("status", 8)] do
    throwError "ordered-storage consumer layout drifted"
  let some writeNow := program.entries.find? (·.ixName == "writeNow")
    | throwError "missing writeNow entry"
  let writeCalls := calls writeNow.ops
  unless writeCalls.size == 1 do
    throwError s!"writeNow: expected one immediate store, got {writeCalls.size}"
  match writeCalls[0]! with
  | .staticStorage (.storeU64 "status" _) => pure ()
  | other => throwError s!"writeNow: unexpected component {repr other}"
  unless !IR.hasStoreField writeNow.ops do
    throwError "immediate store was incorrectly lowered as final state writeback"
  let some around := program.entries.find? (·.ixName == "writeAroundSend")
    | throwError "missing writeAroundSend entry"
  let aroundCalls := calls around.ops
  unless aroundCalls.size == 3 do
    throwError s!"writeAroundSend: expected store/CALL/store, got {aroundCalls.size} calls"
  match aroundCalls[0]!, aroundCalls[1]!, aroundCalls[2]! with
  | .staticStorage (.storeU64 "status" (.lit 2)),
      .nativeFx (.sendEth256 ..),
      .staticStorage (.storeU64 "status" (.lit 1)) => pure ()
  | first, second, third =>
      throwError s!"writeAroundSend effect order drifted: {repr first}; {repr second}; {repr third}"
  unless !IR.hasStoreField around.ops do
    throwError "ordered stores contaminated final state-write detection"
  let yul ←
    match Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  unless yul.contains "sstore(0, 0x2)" &&
      yul.contains "call(gas()" &&
      yul.contains "sstore(0, 0x1)" do
    throwError "ordered storage/CALL Yul fragments missing"

elab "#pf_guard_evm_ordered_storage" : command => expectOrderedStorage

#pf_guard_evm_ordered_storage

end Tests.EvmOrderedStorageSpec
