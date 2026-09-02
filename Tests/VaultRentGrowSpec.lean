import Examples.Svm.VaultRentGrow
import Lean
import ProofForge

/-!
Second `svm-sdk-001` consumer: vault grow with explicit funder top-up.
-/
namespace Tests.VaultRentGrowSpec

open Lean Elab Command
open Examples.Svm.VaultRentGrow
open ProofForge.Svm.Sdk

#pf_build Examples.Svm.VaultRentGrow

#guard vault.resizeDataWithRentTopUp fund targetLen == 0
#guard targetLen == 64

elab "#pf_guard_vault_rent_grow" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.VaultRentGrow with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.cpiAccountCount program >= 2 do
    throwError s!"vault rent grow static prefix too small: {ProofForge.Svm.IR.cpiAccountCount program}"
  let some grow := source.methods.find? (·.ixName == "grow")
    | throwError "missing grow"
  unless grow.paramCount == 0 && grow.retCount == 1 do
    throwError "wrong grow signature"

#pf_guard_vault_rent_grow

end Tests.VaultRentGrowSpec
