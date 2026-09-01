import Examples.RentTopUp
import Lean
import ProofForge

/-!
Focused checks for `svm-sdk-001` rent top-up composition via `Examples.RentTopUp`.
-/
namespace Tests.RentTopUpSpec

open Lean Elab Command
open Examples.RentTopUp
open ProofForge.Svm.Sdk

#pf_build Examples.RentTopUp

#guard dataAccount.topUpRentExempt payer targetLen == 0
#guard dataAccount.resizeDataWithRentTopUp payer targetLen == 0
#guard Sysvar.Rent.minimumBalance 32 == ProofForge.Svm.Runtime.rentExemption 32

elab "#pf_guard_rent_top_up" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.RentTopUp with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.cpiAccountCount program >= 2 do
    throwError s!"rent top-up static prefix too small: {ProofForge.Svm.IR.cpiAccountCount program}"
  let some grow := source.methods.find? (·.ixName == "grow")
    | throwError "missing grow"
  unless grow.paramCount == 0 && grow.retCount == 1 do
    throwError "wrong grow signature"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok text => pure text
    | .error reason => throwError reason
  unless asm.contains "sol_get_rent_sysvar" do
    throwError "expected rent sysvar query in emission"
  unless asm.contains "checked lamport transfer" do
    throwError "expected checked lamport transfer in emission"

#pf_guard_rent_top_up

end Tests.RentTopUpSpec
