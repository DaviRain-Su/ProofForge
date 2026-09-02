import Examples.Svm.LamportTransfer
import Lean
import ProofForge

/-!
Focused checks for the checked SVM lamport-transfer effect via the non-Phoenix
`Examples.Svm.LamportTransfer` consumer. The `#pf_build` commands run the same extraction and sBPF
emission path as the CLI; the `#pf_guard_lamport_transfer` command pins the extraction plan, the
alias-aware Loader-v3 walk contract, and the fail-closed preflight emission. Behavioral bounds
(success, zero amount, writable/owner/balance/overflow failures, duplicate aliases, atomic state
hold) are covered by the Mollusk matrix in `runtime-tests/solana/tests/lamport_transfer.rs`.
-/
namespace Tests.LamportTransferSpec

open Lean Elab Command
open Examples.Svm.LamportTransfer
open ProofForge.Svm.Sdk
open ProofForge.Svm.Runtime

#pf_build Examples.Svm.LamportTransfer
#pf_build Examples.Svm.LamportTransfer

-- Host stubs are irreducible; extraction-time constants never fold into values.
#guard vault.transferLamports recipient 7 == 0
#guard vault.lamports == 0
#guard vault.closeTo recipient == 0

-- Static handle bounds still hold; the component rejects out-of-range and self transfers.
#guard vault.wellFormed && recipient.wellFormed
#guard !(Account.Handle.at 64).wellFormed
#guard
  (ProofForge.Svm.Lamports.Call.transfer 1 2 (5 : UInt64)).wellFormed
    (fun _ => true) 64
#guard
  !(ProofForge.Svm.Lamports.Call.transfer 1 1 (5 : UInt64)).wellFormed
    (fun _ => true) 64
#guard
  !(ProofForge.Svm.Lamports.Call.transfer 1 64 (5 : UInt64)).wellFormed
    (fun _ => true) 64

-- Both header words are read and written exactly once; the canonical spelling is stable.
#guard
  (ProofForge.Svm.Lamports.Call.transfer 1 2 (5 : UInt64)).effects ==
    { reads := #[1, 2], writes := #[1, 2] :
      ProofForge.Svm.AccountStorage.EffectSummary }
#guard
  (ProofForge.Svm.Lamports.Call.transfer 1 2 (5 : UInt64)).canonical
    (fun _ : UInt64 => "amt") == "lamports.transfer.1.2(amt)"
#guard
  (ProofForge.Svm.Lamports.Call.transfer 1 2 (5 : UInt64)).minAccounts
    (fun _ : UInt64 => 0) == 3

/-- Recursive scan for the lowered lamport-transfer component call. -/
partial def opsHaveTransfer (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.svm (.component (.lamports (.transfer 1 2 _)))) => true
    | .ite _ _ _ thn els => opsHaveTransfer thn || opsHaveTransfer els
    | .forBody _ body => opsHaveTransfer body
    | _ => false

/-- Ordered SDK composition markers, retaining the balance snapshot's local identity. -/
inductive CloseStep where
  | balance (snapshot : Nat)
  | resize
  | transfer (amount : ProofForge.Extract.IR.Val)
  | returned (value : ProofForge.Extract.IR.Val)
  deriving Repr

private def closeSteps (ops : Array ProofForge.Extract.IR.Op) : Array CloseStep :=
  ops.filterMap fun
    | .letLocal snapshot (.ext (.svm (.accLamportsN 1)) #[]) => some (.balance snapshot)
    | .ext (.svm (.component (.accountData (.resize 1 (.lit 0))))) => some .resize
    | .ext (.svm (.component (.lamports (.transfer 1 2 amount)))) => some (.transfer amount)
    | .returnU64 value => some (.returned value)
    | _ => none

/-- Extraction and emission contract for the whole example. -/
elab "#pf_guard_lamport_transfer" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.LamportTransfer with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.requiresCanonicalAccountAliases program do
    throwError "lamport transfer did not request canonical account aliases"
  unless ProofForge.Svm.IR.usesWalk program do
    throwError "lamport transfer did not force the walked ABI layout"
  unless ProofForge.Svm.IR.cpiAccountCount program == 3 do
    throwError "lamport transfer static prefix must be max(source, destination) + 1 = 3"
  let moveHasTransfer := source.methods.any fun method =>
    method.ixName == "move" && opsHaveTransfer method.ops
  unless moveHasTransfer do
    throwError "move did not lower to the lamports transfer component call"
  let some close := source.methods.find? (·.ixName == "closeVault")
    | throwError "missing closeVault SDK consumer"
  match closeSteps close.ops with
  | #[.balance snapshot, .resize, .transfer (.local amountLocal), .returned (.local returnLocal)] =>
      unless snapshot == amountLocal && snapshot == returnLocal do
        throwError "closeVault did not reuse its one pre-effect balance snapshot"
  | steps =>
      throwError s!"closeVault did not preserve balance → resize → transfer → return: {repr steps}"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  -- Alias-aware Loader-v3 walk: duplicate entries resolve earlier canonical headers and
  -- advance only 8 bytes; forward/self/malformed aliases exit Custom(1).
  unless asm.contains "walk_alias_0_entry" &&
      asm.contains "walk_full_1_entry" &&
      asm.contains "walk_next_2_entry" &&
      asm.contains "mul64 r3, 8" &&
      asm.contains "add64 r8, 8" do
    throwError "missing alias-aware account walk"
  -- Checked transfer: distinct canonical headers, both writable, program-owned source,
  -- funded debit, overflow-safe credit, all before either store.
  unless asm.contains "; checked lamport transfer acc1 -> acc2" &&
      asm.contains "jne r8, r9, lt_distinct_" &&
      asm.contains "ldxb r1, [r8 + 2]" &&
      asm.contains "ldxb r1, [r9 + 2]" &&
      asm.contains "jge r1, r2, lt_funded_" &&
      asm.contains "jge r4, r3, lt_store_" &&
      asm.contains "stxdw [r8 + 72], r1" &&
      asm.contains "stxdw [r9 + 72], r3" do
    throwError "missing lamport transfer preflight or stores"

#pf_guard_lamport_transfer

end Tests.LamportTransferSpec
