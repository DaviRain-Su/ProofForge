import Examples.MemoryOps
import Lean
import ProofForge

/-!
Focused contracts for official-shaped SVM account-data resize. The source API exposes only a
fixed account handle and a requested length; the target component owns Loader-v3 header mutation,
authorization, bounded growth, and zero initialization. Mollusk covers the corresponding runtime
behavior in `runtime-tests/solana/tests/memory_ops.rs`.
-/

namespace Tests.SvmAccountResizeSpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk

private def external : Account.Handle := Account.Handle.at 1

#guard Memory.maxAccountDataBytes == 10 * 1024 * 1024
#guard AccountData.maxPermittedDataIncrease == 10 * 1024
#guard external.wellFormed
#guard external.resizeData 32 == 0
#guard (AccountData.Call.resize 1 (32 : UInt64)).wellFormed (fun _ => true)
#guard !(AccountData.Call.resize 0 (32 : UInt64)).wellFormed (fun _ => true)
#guard !(AccountData.Call.resize 64 (32 : UInt64)).wellFormed (fun _ => true)
#guard
  (AccountData.Call.resize 1 (32 : UInt64)).effects ==
    { reads := #[1], writes := #[1] : AccountStorage.EffectSummary }
#guard
  (AccountData.Call.resize 1 (32 : UInt64)).canonical (fun _ : UInt64 => "len") ==
    "account-data.resize.1(len)"
#guard
  (AccountData.Call.resize 1 (32 : UInt64)).minAccounts (fun _ : UInt64 => 0) == 2

partial def countResizeCalls (ops : Array ProofForge.Extract.IR.Op) : Nat :=
  ops.foldl (init := 0) fun count op =>
    count + match op with
      | .ext (.svm (.component (.accountData (.resize 1 _)))) => 1
      | .ite _ _ _ thn els => countResizeCalls thn + countResizeCalls els
      | .forBody _ body => countResizeCalls body
      | _ => 0

#pf_build Examples.MemoryOps

elab "#pf_guard_svm_account_resize" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.MemoryOps with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let resizeCount (name : String) : Nat :=
    match source.methods.find? fun method => method.ixName == name with
    | some method => countResizeCalls method.ops
    | none => 0
  unless resizeCount "resizeData" == 1 &&
      resizeCount "resizeThenFill" == 1 &&
      resizeCount "shrinkThenGrow" == 2 do
    throwError "account resize did not stay in the reusable target component"
  unless ProofForge.Svm.IR.requiresCanonicalAccountAliases program &&
      ProofForge.Svm.IR.requiresOriginalAccountDataLengths program &&
      ProofForge.Svm.IR.usesWalk program &&
      ProofForge.Svm.IR.cpiAccountCount program == 2 do
    throwError "account resize did not request the fixed alias-aware invocation-length prefix"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "; checked zero-initializing account-data resize acc1" &&
      asm.contains "call sol_memset_" &&
      asm.contains "stxdw [r8 + 80], r1" &&
      asm.contains "lddw r2, 10485760" &&
      asm.contains "jgt r5, 10240" &&
      asm.contains "stxdw [r10 - 544], r4" &&
      asm.contains "ldxdw r3, [r10 - 544]" &&
      asm.contains "walk_alias_0_entry" &&
      asm.contains "account_resize_writable_" &&
      asm.contains "account_resize_owned_" do
    throwError "account resize authorization, bounds, zeroing, or length store is missing"

#pf_guard_svm_account_resize

end Tests.SvmAccountResizeSpec
