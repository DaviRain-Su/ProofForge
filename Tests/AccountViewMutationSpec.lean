import Examples.AccountViewMutation
import Lean
import ProofForge

/-!
Focused checks for `svm-rt-003`: AccountView + lamport mutation share the combined
variable+aliasing Loader-v3 walk. `#pf_build` exercises extraction/emission; `#pf_guard`
pins detection of both capabilities and the combined-walk markers. Behavioral bounds are covered
by Mollusk in `runtime-tests/solana/tests/account_view_mutation.rs`.
-/
namespace Tests.AccountViewMutationSpec

open Lean Elab Command
open Examples.AccountViewMutation
open ProofForge.Svm.Sdk
open ProofForge.Svm.Runtime

#pf_build Examples.AccountViewMutation

#guard window.peekLamports 0 == 0
#guard vault.transferLamports recipient 7 == 0
#guard window.wellFormed && vault.wellFormed && recipient.wellFormed

elab "#pf_guard_account_view_mutation" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.AccountViewMutation with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.usesAccountView program do
    throwError "combined program must detect AccountView"
  unless ProofForge.Svm.IR.requiresCanonicalAccountAliases program do
    throwError "combined program must declare canonical-alias capability"
  unless ProofForge.Svm.IR.usesWalk program do
    throwError "combined program must force the walked ABI layout"
  unless ProofForge.Svm.IR.cpiAccountCount program == 3 do
    throwError "static prefix must cover state+vault+recipient (3)"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok text => pure text
    | .error reason => throwError reason
  unless asm.contains "view_alias_walk_" do
    throwError "expected combined variable+aliasing walk marker"
  unless asm.contains "view_from_stack_" do
    throwError "expected walked-header AccountView select path"
  unless asm.contains "walk_alias_0_" || asm.contains "walk_full_0_" do
    throwError "expected static-prefix alias resolution labels"
  unless asm.contains "; checked lamport transfer acc1 -> acc2" do
    throwError "expected checked lamport transfer emission"
  let some movePeek := source.methods.find? (·.ixName == "moveAndPeek")
    | throwError "missing moveAndPeek"
  unless movePeek.paramCount == 2 && movePeek.retCount == 1 do
    throwError "wrong moveAndPeek signature"

#pf_guard_account_view_mutation

end Tests.AccountViewMutationSpec
