import Examples.Svm.MemoryOps
import Lean
import ProofForge

/-!
Focused contracts for checked SVM account spans and the four official Solana program-memory
syscalls. Mollusk verifies byte mutation, overlap behavior, exact comparison bits, authorization,
and short-account failure in `runtime-tests/solana/tests/memory_ops.rs`.
-/

namespace Tests.SvmMemorySpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk

private def first : ProofForge.Svm.Sdk.Memory.Span :=
  ProofForge.Svm.Sdk.Memory.Span.accountData 1 0 8
private def second : ProofForge.Svm.Sdk.Memory.Span :=
  ProofForge.Svm.Sdk.Memory.Span.accountData 1 8 8
private def overlap : ProofForge.Svm.Sdk.Memory.Span :=
  ProofForge.Svm.Sdk.Memory.Span.accountData 1 4 8

#guard first.wellFormed
#guard second.wellFormed
#guard !first.overlaps second
#guard first.overlaps overlap
#guard
  !(ProofForge.Svm.Memory.Call.copyNonoverlapping overlap first :
    ProofForge.Svm.Memory.Call UInt64).wellFormed (fun _ => true)
#guard
  (ProofForge.Svm.Memory.Call.move overlap first :
    ProofForge.Svm.Memory.Call UInt64).wellFormed (fun _ => true)
#guard
  !(ProofForge.Svm.Sdk.Memory.Span.accountData 64 0 8).wellFormed
#guard
  !(ProofForge.Svm.Sdk.Memory.Span.accountData
    1 ProofForge.Svm.Memory.maxAccountDataBytes 1).wellFormed

-- Host stubs do not pretend to own account bytes.
#guard ProofForge.Svm.Sdk.Memory.copyNonoverlapping second first == 0
#guard ProofForge.Svm.Sdk.Memory.move overlap first == 0
#guard ProofForge.Svm.Sdk.Memory.set first 0xaa == 0
#guard ProofForge.Svm.Sdk.Memory.compareI32Bits first second == 0

#pf_build Examples.Svm.MemoryOps

elab "#pf_guard_svm_memory" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.MemoryOps with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless program.methods.any fun method => method.ops.any fun
      | .component (.memory (.copyNonoverlapping _ _)) => true
      | _ => false do
    throwError "memory copy did not lower through the target component"
  unless program.methods.any fun method => method.ops.any fun
      | .component (.memory (.move _ _)) => true
      | _ => false do
    throwError "memory move did not lower through the target component"
  unless program.methods.any fun method => method.ops.any fun
      | .component (.memory (.set _ _)) => true
      | _ => false do
    throwError "memory set did not lower through the target component"
  let compareIsMemory := source.methods.any fun method => method.ops.any fun
    | .returnU64 (.ext (.svm (.component (.memory (.compare _ _)))) #[]) => true
    | _ => false
  unless compareIsMemory do
    throwError "memory compare did not lower through the target query"
  unless ProofForge.Svm.IR.usesWalk program &&
      ProofForge.Svm.IR.cpiAccountCount program == 2 do
    throwError "memory spans did not request the fixed account walk"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "call sol_memcpy_" && asm.contains "call sol_memmove_" &&
      asm.contains "call sol_memcmp_" && asm.contains "call sol_memset_" &&
      asm.contains "checked account span acc=1" &&
      asm.contains "memory_writable_" && asm.contains "memory_owned_" do
    throwError "official memory syscalls or checked span gates are missing"

end Tests.SvmMemorySpec
