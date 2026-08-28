import Examples.AccountView
import Lean
import ProofForge

/-!
Focused checks for the SVM-RT-1 bounded remaining-account view via the non-Phoenix
`Examples.AccountView` consumer. The `#pf_build` commands run the same extraction and sBPF
emission path as the CLI; the `#pf_guard_account_view` command pins the extraction plan, the
runtime walk contract, and the fail-closed emission markers. Behavioral bounds (capacity OOB,
available-count OOB, duplicate keys, short data, signer/writable/owner, atomic state hold) are
covered by the Mollusk matrix in `runtime-tests/solana/tests/account_view.rs`.
-/
namespace Tests.AccountViewSpec

open Lean Elab Command
open Examples.AccountView
open ProofForge.Svm.AccountView.Source
open ProofForge.Svm.Runtime

#pf_build Examples.AccountView
#pf_build Examples.AccountView

-- Host stubs are irreducible; extraction-time constants never fold into values.
#guard window.peekData 0 0 == 0
#guard window.peekKey 3 1 == 0
#guard window.peekSigner 2 == 0
#guard window.ownedBySelf 0 == 0

-- The facade erases to the target-owned component query; the descriptor stays compile-time.
#guard window.wellFormed
#guard (View.bounded 1 63).wellFormed
#guard !({ base := 0, capacity := 4 } : View).wellFormed
#guard !({ base := 1, capacity := 0 } : View).wellFormed
#guard !({ base := 60, capacity := 8 } : View).wellFormed
#guard !({ base := 64, capacity := 1 } : View).wellFormed

-- Query-level fail-closed shape: key words are bounded to one 32-byte key.
#guard
  (ProofForge.Svm.AccountView.Query.header { base := 1, capacity := 4 } (.key 3)).wellFormed
#guard
  !(ProofForge.Svm.AccountView.Query.header
      { base := 1, capacity := 4 } (.key 4)).wellFormed
#guard
  (ProofForge.Svm.AccountView.Query.dataWord { base := 1, capacity := 4 } 0).canonical
    (fun _ : UInt64 => "idx") (#[0] : Array UInt64) == "avd.1.4.0(idx)"
#guard
  (ProofForge.Svm.AccountView.Query.ownerIsSelf { base := 1, capacity := 4 }).canonical
    (fun _ : UInt64 => "idx") (#[0] : Array UInt64) == "avo.1.4(idx)"

/-- Extraction and emission contract for the whole example. -/
elab "#pf_guard_account_view" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.AccountView with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.usesAccountView program do
    throwError "account view was not detected in the extracted program"
  unless ProofForge.Svm.IR.usesWalk program do
    throwError "account view did not force the walked ABI layout"
  unless ProofForge.Svm.IR.cpiAccountCount program == 2 do
    throwError "account view static prefix must be base + 1 = 2"
  let some peek := source.methods.find? (·.ixName == "peek")
    | throwError "missing peek method"
  unless peek.paramCount == 1 && peek.retCount == 1 do
    throwError "wrong peek signature"
  let viewQuery? : ProofForge.Extract.IR.Op → Option ProofForge.Svm.Component.Query
    | .returnU64 (.ext (.svm (.component query)) _) => some query
    | _ => none
  let queryIsView :=
    match peek.ops[0]? with
    | some op =>
        match viewQuery? op with
        | some (.accountView _) => true
        | _ => false
    | none => false
  unless queryIsView do
    throwError "peek did not lower to the account-view component query"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  -- Runtime-safe selection: compile-time capacity and available-account checks before the walk.
  unless asm.contains "select bounded remaining account base=1 capacity=4" &&
      asm.contains "lddw r3, 4" &&
      asm.contains "ldxdw r2, [r6 + NUM_ACCOUNTS]" &&
      asm.contains "jge r9, r2, fail_view_index" do
    throwError "missing account-view index validation"
  -- Bounded account-view walk contract: runtime NUM_ACCOUNTS, hard-bounded by the lock limit.
  unless asm.contains "jgt r9, r1, err_unknown_disc" &&
      asm.contains "jlt r9, 2, err_unknown_disc" &&
      asm.contains "view_walk_entry" &&
      asm.contains "view_done_entry" &&
      asm.contains "stxdw [r10 - 528], r8" do
    throwError "missing bounded runtime account-count walk"
  -- Header/data access through the walked header pointer.
  unless asm.contains "load view header k0" &&
      asm.contains "load view data word 0" &&
      asm.contains "view ownerIsSelf" do
    throwError "missing account-view field access"

end Tests.AccountViewSpec