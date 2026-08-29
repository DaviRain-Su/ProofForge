import Examples.AccountView
import Examples.MemoryOps
import Examples.TransientPair
import Lean
import ProofForge

/-!
Focused lowering and emitter guards for the source-visible invocation-local byte buffer/writer.
Mollusk owns live heap mutation, byte ordering, bounds, range, stale-handle, and OOM behavior.
-/

namespace Tests.SvmTransientBytesSpec

open Lean Elab Command
open ProofForge.Svm

private def bytes4 : TransientBytes.Config := { capacity := 4 }
private def bytes12 : TransientBytes.Config := { capacity := 12 }
private def bytesSmall : TransientBytes.Config := { capacity := 3 }

#guard bytes4.wellFormed
#guard bytes12.wellFormed
#guard (TransientBytes.Call.appendLe64 bytes12 7 :
  TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  !((TransientBytes.Call.appendLe64 bytesSmall 7 :
      TransientBytes.Call UInt64).wellFormed (fun _ => true))
#guard
  (TransientBytes.Call.begin bytes4 : TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientBytes.Call.push bytes4 255 : TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientBytes.Call.set bytes4 0 9 : TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientBytes.Call.truncate bytes4 2 :
    TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  (TransientBytes.Call.truncate bytes4 2 :
    TransientBytes.Call UInt64).canonical toString == "tbyte.truncate.4(2)"
#guard
  (TransientBytes.Call.logData bytes4 : TransientBytes.Call UInt64).wellFormed (fun _ => true)
#guard
  !((TransientBytes.Call.logData { capacity := 0 } :
      TransientBytes.Call UInt64).wellFormed (fun _ => true))
#guard
  (TransientBytes.Call.logData bytes4 : TransientBytes.Call UInt64).canonical (fun _ => "v") ==
    "tbyte.logData.4"
#guard (TransientBytes.Query.length bytes4).wellFormed
#guard (TransientBytes.Query.get bytes4).arity == 1
#guard (TransientBytes.Query.pop bytes4).arity == 0
#guard
  (TransientBytes.Query.get bytes4).canonical (fun _ : UInt64 => "i") #[0] ==
    "tbyte.get.4(i)"
#guard
  (TransientBytes.Query.pop bytes4).canonical (fun _ : UInt64 => "unused") #[] ==
    "tbyte.pop.4"

#pf_build Examples.MemoryOps
#pf_build Examples.TransientPair

private def bytesStep : ProofForge.Svm.IR.Op → Option String
  | .component (.transientBytes (.begin _)) => some "begin"
  | .component (.transientBytes (.push _ _)) => some "push"
  | .component (.transientBytes (.appendLe64 _ _)) => some "appendLe64"
  | .component (.transientBytes (.set _ _ _)) => some "set"
  | .component (.transientBytes (.truncate _ _)) => some "truncate"
  | .component (.transientBytes (.clear _)) => some "clear"
  | .component (.transientBytes (.finish _)) => some "finish"
  | .component (.transientBytes (.logData _)) => some "logData"
  | .letLocal _ (.ext (.component (.transientBytes (.length _))) #[]) => some "length"
  | .letLocal _ (.ext (.component (.transientBytes (.get _))) #[_]) => some "get"
  | .letLocal _ (.ext (.component (.transientBytes (.pop _))) #[]) => some "pop"
  | .returnU64 (.ext (.component (.transientBytes (.length _))) #[]) => some "length"
  | .returnU64 (.ext (.component (.transientBytes (.get _))) #[_]) => some "get"
  | .returnU64 (.ext (.component (.transientBytes (.pop _))) #[]) => some "pop"
  | _ => none

private def taggedStep : ProofForge.Svm.IR.Op → Option String
  | .component (.transientVec (.begin _)) => some "v.begin"
  | .component (.transientVec (.push _ _)) => some "v.push"
  | .component (.transientVec (.set _ _ _)) => some "v.set"
  | .component (.transientVec (.truncate _ _)) => some "v.truncate"
  | .component (.transientVec (.clear _)) => some "v.clear"
  | .component (.transientVec (.finish _)) => some "v.finish"
  | .component (.transientBytes (.begin _)) => some "b.begin"
  | .component (.transientBytes (.push _ _)) => some "b.push"
  | .component (.transientBytes (.appendLe64 _ _)) => some "b.appendLe64"
  | .component (.transientBytes (.set _ _ _)) => some "b.set"
  | .component (.transientBytes (.truncate _ _)) => some "b.truncate"
  | .component (.transientBytes (.clear _)) => some "b.clear"
  | .component (.transientBytes (.finish _)) => some "b.finish"
  | .component (.transientBytes (.logData _)) => some "b.logData"
  | .letLocal _ (.ext (.component (.transientVec _)) _) => some "v.query"
  | .letLocal _ (.ext (.component (.transientBytes _)) _) => some "b.query"
  | .returnU64 (.ext (.component (.transientVec _)) _) => some "v.query"
  | .returnU64 (.ext (.component (.transientBytes _)) _) => some "b.query"
  | _ => none

private def filtered (step : ProofForge.Svm.IR.Op → Option String)
    (method : ProofForge.Svm.IR.Method) : Array String :=
  method.ops.filterMap step

elab "#pf_guard_transient_bytes" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.MemoryOps with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let hasCall (predicate : TransientBytes.Call ProofForge.Svm.Ops.Val → Bool) :=
    program.methods.any fun method => method.ops.any fun
      | .component (.transientBytes call) => predicate call
      | _ => false
  unless hasCall (fun | .begin _ => true | _ => false) &&
      hasCall (fun | .push _ _ => true | _ => false) &&
      hasCall (fun | .appendLe64 _ _ => true | _ => false) &&
      hasCall (fun | .set _ _ _ => true | _ => false) &&
      hasCall (fun | .truncate _ _ => true | _ => false) &&
      hasCall (fun | .clear _ => true | _ => false) &&
      hasCall (fun | .logData _ => true | _ => false) &&
      hasCall (fun | .finish _ => true | _ => false) do
    throwError "transient byte calls did not stay behind the component bridge"
  let hasLength := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientBytes (.length _)))) #[]) => true
    | .returnU64 (.ext (.svm (.component (.transientBytes (.length _)))) #[]) => true
    | _ => false
  let hasGet := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientBytes (.get _)))) #[_]) => true
    | .returnU64 (.ext (.svm (.component (.transientBytes (.get _)))) #[_]) => true
    | _ => false
  let hasPop := source.methods.any fun method => method.ops.any fun
    | .letLocal _ (.ext (.svm (.component (.transientBytes (.pop _)))) #[]) => true
    | .returnU64 (.ext (.svm (.component (.transientBytes (.pop _)))) #[]) => true
    | _ => false
  unless hasLength && hasGet && hasPop do
    throwError "transient byte queries did not stay behind the component bridge"
  let some setGet := program.methods.find? (·.ixName == "bytesSetGet")
    | throwError "missing bytesSetGet method"
  unless filtered bytesStep setGet == #["begin", "push", "push", "set", "get", "finish"] do
    throwError "bytesSetGet effects were not preserved in source order"
  let some appendGet := program.methods.find? (·.ixName == "bytesAppendLe64")
    | throwError "missing bytesAppendLe64 method"
  unless filtered bytesStep appendGet == #["begin", "appendLe64", "get", "finish"] do
    throwError "bytesAppendLe64 effects were not preserved in source order"
  let some truncateLength := program.methods.find? (·.ixName == "bytesLengthAfterTruncate")
    | throwError "missing bytesLengthAfterTruncate method"
  unless filtered bytesStep truncateLength ==
      #["begin", "push", "push", "truncate", "length", "finish"] do
    throwError "bytesLengthAfterTruncate effects were not preserved in source order"
  let some pop := program.methods.find? (·.ixName == "bytesPop")
    | throwError "missing bytesPop method"
  unless filtered bytesStep pop == #["begin", "push", "push", "pop", "finish"] do
    throwError "bytesPop effects were not preserved in source order"
  let some popEmpty := program.methods.find? (·.ixName == "bytesPopEmpty")
    | throwError "missing bytesPopEmpty method"
  unless filtered bytesStep popEmpty == #["begin", "pop"] do
    throwError "bytesPopEmpty did not preserve empty-pop validation order"
  let some logData := program.methods.find? (·.ixName == "bytesLogData")
    | throwError "missing bytesLogData method"
  unless filtered bytesStep logData ==
      #["begin", "appendLe64", "push", "length", "logData", "finish"] do
    throwError "bytesLogData did not preserve its bounded writer and syscall effects in source order"
  let some afterFinish := program.methods.find? (·.ixName == "bytesAfterFinish")
    | throwError "missing bytesAfterFinish method"
  unless filtered bytesStep afterFinish == #["begin", "finish", "length"] do
    throwError "bytesAfterFinish did not preserve stale-handle validation order"
  -- Same-kind multi-handle evidence: two compile-time Bytes slots in the dedicated
  -- `Examples.TransientPair` module decode through the same component bridge with distinct
  -- erased words and per-slot isolation.
  let pairSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.TransientPair with
    | .ok program => pure program
    | .error reason => throwError reason
  let pairProgram ←
    match ProofForge.Svm.IR.fromExtracted pairSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let some pairSetGet := pairProgram.methods.find? (·.ixName == "bytesPairSetGet")
    | throwError "missing bytesPairSetGet method"
  unless filtered bytesStep pairSetGet ==
      #["begin", "begin", "push", "push", "push", "push", "set", "get", "get", "finish",
        "finish"] do
    throwError "bytesPairSetGet did not interleave both same-kind byte slots in source order"
  let pairBegins := pairSetGet.ops.filterMap fun
    | .component (.transientBytes (.begin config)) => some config
    | _ => none
  unless pairBegins.size == 2 && pairBegins[0]! != pairBegins[1]! &&
      pairBegins[0]!.slot == 0 && pairBegins[1]!.slot == 1 &&
      pairBegins[0]!.fixedVec == pairBegins[1]!.fixedVec do
    throwError "bytesPairSetGet did not decode two disjoint same-kind byte handles"
  let some pairTruncate := pairProgram.methods.find?
      (·.ixName == "bytesPairTruncateIsolated")
    | throwError "missing bytesPairTruncateIsolated method"
  unless filtered bytesStep pairTruncate ==
      #["begin", "begin", "push", "push", "push", "truncate", "length", "length", "finish",
        "finish"] do
    throwError "bytesPairTruncateIsolated did not isolate truncate per slot"
  let some pairOom := pairProgram.methods.find? (·.ixName == "bytesPairOom")
    | throwError "missing bytesPairOom method"
  unless filtered bytesStep pairOom == #["begin", "begin"] &&
      (pairOom.ops.countP fun
        | .component (.transientBytes (.begin config)) => config.slot == 1
        | _ => false) == 1 do
    throwError "bytesPairOom did not exhaust the heap from the alternate byte slot"
  let some unbegun := pairProgram.methods.find? (·.ixName == "bytesPairUnbegunSlot")
    | throwError "missing bytesPairUnbegunSlot method"
  unless filtered bytesStep unbegun == #["begin", "push"] do
    throwError "bytesPairUnbegunSlot did not open exactly one byte slot"
  let some withVector := program.methods.find? (·.ixName == "vectorWithBytes")
    | throwError "missing vectorWithBytes method"
  unless filtered taggedStep withVector ==
      #["v.begin", "b.begin", "b.push", "v.push", "b.get", "v.get", "v.finish", "b.finish"] do
    throwError "vectorWithBytes did not interleave both handles in source order"
  let accountSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.AccountView with
    | .ok program => pure program
    | .error reason => throwError reason
  let accountProgram ←
    match ProofForge.Svm.IR.fromExtracted accountSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let some stageBytes := accountProgram.methods.find? (·.ixName == "stageSelectedBytes")
    | throwError "missing AccountView.stageSelectedBytes method"
  unless filtered taggedStep stageBytes == #["b.begin", "b.appendLe64", "b.query", "b.finish"] do
    throwError "AccountView stageSelectedBytes effects were not preserved in source order"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "official Solana downward bump allocation bytes=4 align=1" &&
      asm.contains "transient_bytes_heap_position_" &&
      asm.contains "transient_bytes_push_range_" &&
      asm.contains "transient_bytes_push_room_" &&
      asm.contains "transient_bytes_get_bounds_" &&
      asm.contains "transient_bytes_truncate_done_" &&
      asm.contains "transient_bytes_pop_nonempty_" &&
      asm.contains "one sol_log_data field views the active 12-byte payload buffer" &&
      asm.contains "call sol_log_data" &&
      asm.contains "stxdw [r9 + 0], r1" && asm.contains "stxdw [r9 + 8], r1" &&
      asm.contains "stxb [r9 + 0], r1" &&
      asm.contains "lddw r0, 0x1211" && asm.contains "lddw r0, 0x1212" &&
      asm.contains "lddw r0, 0x1213" && asm.contains "lddw r0, 0x1214" do
    throwError "bounded byte allocator, mutation, canonical range, or explicit failure gates are missing"
  -- The dedicated multi-handle program: same-kind second-slot metadata cells (pointer 2432,
  -- length 2440, active 2456) back the shared lifecycle, below the unchanged
  -- `sol_log_data` descriptor window at 2465..2480.
  let pairAsm ←
    match ProofForge.Svm.Emit.emitAsm pairProgram with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless pairAsm.contains "ldxdw r9, [r10 - 2432]" && pairAsm.contains "ldxdw r2, [r10 - 2440]" &&
      pairAsm.contains "stxdw [r10 - 2440], r2" &&
      pairAsm.contains "stxb [r10 - 2432]" == false do
    throwError "same-kind second-slot byte metadata cells are missing"
  unless pairAsm.contains "add64 r9, -2480" && pairAsm.contains "lddw r0, 0x1213" do
    throwError "second-slot byte handles did not keep the descriptor and state gates"

end Tests.SvmTransientBytesSpec
