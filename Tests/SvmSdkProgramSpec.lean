import ProofForge.Svm.Sdk.AssociatedToken
import ProofForge.Svm.Sdk.Memo
import Examples.Ata
import Examples.Memo

open Lean Elab Command

namespace Tests.SvmSdkProgramSpec

open ProofForge.Svm.Sdk

#guard AssociatedToken.createIdempotent == 0
#guard Memo.writeOk == 0

private def expectCanonical (module : Name) (expected : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let actual := ProofForge.Svm.IR.digestHex program
  unless actual == expected do
    throwError s!"{module}: SDK facade changed canonical IR: {actual}"

elab "#pf_guard_svm_program_facades" : command => do
  expectCanonical `Examples.Ata "574dc90c21ca9723"
  expectCanonical `Examples.Memo "26a3540da902ccb5"

#pf_guard_svm_program_facades

end Tests.SvmSdkProgramSpec
