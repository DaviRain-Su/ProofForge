import ProofForge
import ProofForge.Svm.IR
import Examples.SvmExceptErgonomics

open Lean Elab Command

elab "#pf_guard_svm_except_ergonomics" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.SvmExceptErgonomics with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless program.methods.any (·.ixName == "addViaAndThen") do
    throwError "SVM Except ergonomics missing addViaAndThen entry"
  logInfo m!"proofforge-svm-except-ergonomics: digest = {ProofForge.Svm.IR.digestHex program}"

#pf_guard_svm_except_ergonomics
