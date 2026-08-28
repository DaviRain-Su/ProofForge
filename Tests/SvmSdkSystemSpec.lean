import ProofForge.Svm.Sdk.System
import Examples.SysAlloc
import Examples.Nonce

open Lean Elab Command

namespace Tests.SvmSdkSystemSpec

open ProofForge.Svm.Sdk

#guard System.assign == 0
#guard System.allocate 16 == 0
#guard System.allocate 0 == 0
#guard System.advanceNonce == 0

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

elab "#pf_guard_svm_system_facades" : command => do
  expectCanonical `Examples.SysAlloc "dbb2269b9ac57a3"
  expectCanonical `Examples.Nonce "5746ebbdd382bd56"

#pf_guard_svm_system_facades

end Tests.SvmSdkSystemSpec
