import Examples.AccountView
import Examples.MemoryOps
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
#guard (TransientVec.Query.length vector2).wellFormed
#guard (TransientVec.Query.get vector2).arity == 1
#guard
  (TransientVec.Query.get vector2).canonical (fun _ : UInt64 => "i") #[0] ==
    "tv64.get.2(i)"

#pf_build Examples.MemoryOps

private def vectorStep : ProofForge.Svm.IR.Op → Option String
  | .component (.transientVec (.begin _)) => some "begin"
  | .component (.transientVec (.push _ _)) => some "push"
  | .component (.transientVec (.set _ _ _)) => some "set"
  | .component (.transientVec (.clear _)) => some "clear"
  | .component (.transientVec (.finish _)) => some "finish"
  | .letLocal _ (.ext (.component (.transientVec (.length _))) #[]) => some "length"
  | .letLocal _ (.ext (.component (.transientVec (.get _))) #[_]) => some "get"
  | .returnU64 (.ext (.component (.transientVec (.length _))) #[]) => some "length"
  | .returnU64 (.ext (.component (.transientVec (.get _))) #[_]) => some "get"
  | _ => none

private def vectorSteps (method : ProofForge.Svm.IR.Method) : Array String :=
  method.ops.filterMap vectorStep

elab "#pf_guard_transient_vector" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.MemoryOps with
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
  unless hasLength && hasGet do
    throwError "transient vector queries did not stay behind the component bridge"
  let some setGet := program.methods.find? (·.ixName == "vectorSetGet")
    | throwError "missing vectorSetGet method"
  unless vectorSteps setGet == #["begin", "push", "push", "set", "get", "finish"] do
    throwError "vectorSetGet effects were not preserved in source order"
  let some clearLength := program.methods.find? (·.ixName == "vectorLengthAfterClear")
    | throwError "missing vectorLengthAfterClear method"
  unless vectorSteps clearLength == #["begin", "push", "clear", "length", "finish"] do
    throwError "vectorLengthAfterClear effects were not preserved in source order"
  let some afterFinish := program.methods.find? (·.ixName == "vectorAfterFinish")
    | throwError "missing vectorAfterFinish method"
  unless vectorSteps afterFinish == #["begin", "finish", "length"] do
    throwError "vectorAfterFinish did not preserve stale-handle validation order"
  let accountSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.AccountView with
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
      asm.contains "lddw r0, 0x1201" && asm.contains "lddw r0, 0x1202" &&
      asm.contains "lddw r0, 0x1203" do
    throwError "bounded vector allocator, mutation, or explicit failure gates are missing"

end Tests.SvmTransientVectorSpec
