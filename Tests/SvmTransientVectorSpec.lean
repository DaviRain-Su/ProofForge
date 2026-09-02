import Examples.Svm.AccountView
import Examples.Svm.MemoryOps
import Examples.Svm.TransientPair
import Lean
import ProofForge

/-!
Focused lowering and emitter guards for the source-visible invocation-local `Vector64`. Mollusk
owns live heap mutation, bounds, stale-handle, and OOM behavior.
-/

namespace Tests.SvmTransientVectorSpec

open Lean Elab Command
open ProofForge.Svm

private def vector2 : TransientVec.Config := { capacity := 2 }

#guard vector2.wellFormed
#guard
  (TransientVec.Call.begin vector2 : TransientVec.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientVec.Call.push vector2 7 : TransientVec.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientVec.Call.set vector2 0 9 : TransientVec.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientVec.Call.truncate vector2 1 : TransientVec.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientVec.Call.truncate vector2 1 : TransientVec.Call UInt64).canonical toString ==
    "tv64.truncate.2(1)"
#guard (TransientVec.Query.length vector2).wellFormed
#guard (TransientVec.Query.get vector2).arity == 1
#guard (TransientVec.Query.pop vector2).arity == 0
#guard
  (TransientVec.Query.get vector2).canonical (fun _ : UInt64 => "i") #[0] ==
    "tv64.get.2(i)"
#guard
  (TransientVec.Query.pop vector2).canonical (fun _ : UInt64 => "unused") #[] ==
    "tv64.pop.2"

#pf_build Examples.Svm.MemoryOps
#pf_build Examples.Svm.TransientPair

private def vectorStep : ProofForge.Svm.IR.Op → Option String
  | .component (.transientVec (.begin _)) => some "begin"
  | .component (.transientVec (.push _ _)) => some "push"
  | .component (.transientVec (.set _ _ _)) => some "set"
  | .component (.transientVec (.truncate _ _)) => some "truncate"
  | .component (.transientVec (.clear _)) => some "clear"
  | .component (.transientVec (.finish _)) => some "finish"
  | .letLocal _ (.ext (.component (.transientVec (.length _))) #[]) => some "length"
  | .letLocal _ (.ext (.component (.transientVec (.get _))) #[_]) => some "get"
  | .letLocal _ (.ext (.component (.transientVec (.pop _))) #[]) => some "pop"
  | .returnU64 (.ext (.component (.transientVec (.length _))) #[]) => some "length"
  | .returnU64 (.ext (.component (.transientVec (.get _))) #[_]) => some "get"
  | .returnU64 (.ext (.component (.transientVec (.pop _))) #[]) => some "pop"
  | _ => none

private def vectorSteps (method : ProofForge.Svm.IR.Method) : Array String :=
  method.ops.filterMap vectorStep

elab "#pf_guard_transient_vector" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.MemoryOps with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let hasCall (predicate : TransientVec.Call ProofForge.Svm.Ops.Val → Bool) :=
    program.methods.any fun method => method.ops.any fun
      | .component (.transientVec call) => predicate call
      | _ => false
  unless hasCall (fun | .begin _ => true | _ => false) &&
      hasCall (fun | .push _ _ => true | _ => false) &&
      hasCall (fun | .set _ _ _ => true | _ => false) &&
      hasCall (fun | .truncate _ _ => true | _ => false) &&
      hasCall (fun | .clear _ => true | _ => false) &&
      hasCall (fun | .finish _ => true | _ => false) do
    throwError "transient vector calls did not stay behind the component bridge"
  let hasLength := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientVec (.length _)))) #[]) => true
    | .returnU64 (.ext (.svm (.component (.transientVec (.length _)))) #[]) => true
    | _ => false
  let hasGet := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientVec (.get _)))) #[_]) => true
    | .returnU64 (.ext (.svm (.component (.transientVec (.get _)))) #[_]) => true
    | _ => false
  let hasPop := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientVec (.pop _)))) #[]) => true
    | .returnU64 (.ext (.svm (.component (.transientVec (.pop _)))) #[]) => true
    | _ => false
  unless hasLength && hasGet && hasPop do
    throwError "transient vector queries did not stay behind the component bridge"
  let some setGet := program.methods.find? (·.ixName == "vectorSetGet")
    | throwError "missing vectorSetGet method"
  unless vectorSteps setGet == #["begin", "push", "push", "set", "get", "finish"] do
    throwError "vectorSetGet effects were not preserved in source order"
  let some clearLength := program.methods.find? (·.ixName == "vectorLengthAfterClear")
    | throwError "missing vectorLengthAfterClear method"
  unless vectorSteps clearLength == #["begin", "push", "clear", "length", "finish"] do
    throwError "vectorLengthAfterClear effects were not preserved in source order"
  let some truncateLength := program.methods.find? (·.ixName == "vectorLengthAfterTruncate")
    | throwError "missing vectorLengthAfterTruncate method"
  unless vectorSteps truncateLength ==
      #["begin", "push", "push", "truncate", "length", "finish"] do
    throwError "vectorLengthAfterTruncate effects were not preserved in source order"
  let some pop := program.methods.find? (·.ixName == "vectorPop")
    | throwError "missing vectorPop method"
  unless vectorSteps pop == #["begin", "push", "push", "pop", "finish"] do
    throwError "vectorPop effects were not preserved in source order"
  let some popEmpty := program.methods.find? (·.ixName == "vectorPopEmpty")
    | throwError "missing vectorPopEmpty method"
  unless vectorSteps popEmpty == #["begin", "pop"] do
    throwError "vectorPopEmpty did not preserve empty-pop validation order"
  let some afterFinish := program.methods.find? (·.ixName == "vectorAfterFinish")
    | throwError "missing vectorAfterFinish method"
  unless vectorSteps afterFinish == #["begin", "finish", "length"] do
    throwError "vectorAfterFinish did not preserve stale-handle validation order"
  -- Same-kind multi-handle evidence: two compile-time Vector64 slots decode through the same
  -- component bridge with distinct erased words and the shared lifecycle order. The evidence
  -- lives in the dedicated `Examples.Svm.TransientPair` consumer.
  let pairSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.TransientPair with
    | .ok program => pure program
    | .error reason => throwError reason
  let pairProgram ←
    match ProofForge.Svm.IR.fromExtracted pairSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let some pairSetGet := pairProgram.methods.find? (·.ixName == "vectorPairSetGet")
    | throwError "missing vectorPairSetGet method"
  unless vectorSteps pairSetGet ==
      #["begin", "begin", "push", "push", "push", "push", "set", "get", "get", "finish",
        "finish"] do
    throwError "vectorPairSetGet did not interleave both same-kind slots in source order"
  let pairBegins := pairSetGet.ops.filterMap fun
    | .component (.transientVec (.begin config)) => some config
    | _ => none
  unless pairBegins.size == 2 && pairBegins[0]! != pairBegins[1]! &&
      pairBegins[0]!.slot == 0 && pairBegins[1]!.slot == 1 &&
      pairBegins[0]!.fixedVec == pairBegins[1]!.fixedVec do
    throwError "vectorPairSetGet did not decode two disjoint same-kind handles"
  let some pairClear := pairProgram.methods.find? (·.ixName == "vectorPairClearIsolated")
    | throwError "missing vectorPairClearIsolated method"
  unless vectorSteps pairClear ==
      #["begin", "begin", "push", "push", "push", "clear", "length", "length", "finish",
        "finish"] do
    throwError "vectorPairClearIsolated did not isolate clear per slot"
  let some pairTruncate := pairProgram.methods.find?
      (·.ixName == "vectorPairTruncateIsolated")
    | throwError "missing vectorPairTruncateIsolated method"
  unless vectorSteps pairTruncate ==
      #["begin", "begin", "push", "push", "push", "push", "truncate", "length", "length",
        "get", "finish", "finish"] do
    throwError "vectorPairTruncateIsolated did not isolate truncate per slot"
  let some pairPop := pairProgram.methods.find? (·.ixName == "vectorPairPopIsolated")
    | throwError "missing vectorPairPopIsolated method"
  unless vectorSteps pairPop ==
      #["begin", "begin", "push", "push", "push", "push", "pop", "pop", "finish", "finish"] do
    throwError "vectorPairPopIsolated did not isolate pop per slot"
  let some pairFinish := pairProgram.methods.find?
      (·.ixName == "vectorPairFinishIsolated")
    | throwError "missing vectorPairFinishIsolated method"
  unless vectorSteps pairFinish == #["begin", "begin", "push", "finish", "get", "finish"] do
    throwError "vectorPairFinishIsolated did not keep slot 1 live after finishing slot 0"
  let some fourPairs := pairProgram.methods.find? (·.ixName == "fourTransientPairs")
    | throwError "missing fourTransientPairs method"
  unless (vectorSteps fourPairs).count "begin" == 2 && (vectorSteps fourPairs).count "get" == 4 do
    throwError "fourTransientPairs did not keep both vector slots live"
  let some pairOom := pairProgram.methods.find? (·.ixName == "vectorPairOom")
    | throwError "missing vectorPairOom method"
  unless vectorSteps pairOom == #["begin", "begin"] do
    throwError "vectorPairOom did not begin both same-kind slots"
  unless (pairOom.ops.countP fun
        | .component (.transientVec (.begin config)) => config.slot == 1
        | _ => false) == 1 &&
      pairOom.ops.any fun
        | .component (.transientVec (.begin config)) => config.slot == 0 && config.payload == 100
        | _ => false do
    throwError "vectorPairOom did not exhaust the heap from the alternate slot"
  let some unbegun := pairProgram.methods.find? (·.ixName == "vectorPairUnbegunSlot")
    | throwError "missing vectorPairUnbegunSlot method"
  unless vectorSteps unbegun == #["begin", "push"] do
    throwError "vectorPairUnbegunSlot did not open exactly one slot"
  let accountSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.AccountView with
    | .ok program => pure program
    | .error reason => throwError reason
  let accountProgram ←
    match ProofForge.Svm.IR.fromExtracted accountSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let some stageSelected := accountProgram.methods.find? (·.ixName == "stageSelected")
    | throwError "missing AccountView.stageSelected method"
  unless vectorSteps stageSelected == #["begin", "push", "get", "finish"] do
    throwError "AccountView transient-vector effects were not preserved in source order"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "official Solana downward bump allocation bytes=16 align=8" &&
      asm.contains "transient_vec_heap_position_" &&
      asm.contains "transient_vec_push_room_" &&
      asm.contains "transient_vec_get_bounds_" &&
      asm.contains "transient_vec_truncate_done_" &&
      asm.contains "transient_vec_pop_nonempty_" &&
      asm.contains "lddw r0, 0x1201" && asm.contains "lddw r0, 0x1202" &&
      asm.contains "lddw r0, 0x1203" do
    throwError "bounded vector allocator, mutation, or explicit failure gates are missing"
  -- The dedicated multi-handle program: same-kind second-slot metadata cells (pointer 2344,
  -- length 2352, active 2368) back the shared lifecycle interpreter, and the same program's OOM
  -- and unbegun-slot methods pin the explicit failures.
  let pairAsm ←
    match ProofForge.Svm.Emit.emitAsm pairProgram with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless pairAsm.contains "ldxdw r9, [r10 - 2344]" && pairAsm.contains "ldxdw r2, [r10 - 2352]" &&
      pairAsm.contains "stxdw [r10 - 2352], r2" && pairAsm.contains "stxdw [r10 - 2368], r1" &&
      pairAsm.contains "lddw r0, 0x1203" do
    throwError "same-kind second-slot metadata cells are missing"

end Tests.SvmTransientVectorSpec
