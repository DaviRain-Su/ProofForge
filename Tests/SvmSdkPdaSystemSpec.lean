import ProofForge.Svm.Sdk.Pda
import ProofForge.Svm.Sdk.System
import Examples.Pda
import Examples.Transfer
import Examples.Create
import Examples.CreatePda

open Lean Elab Command

namespace Tests.SvmSdkPdaSystemSpec

open ProofForge.Svm.Sdk

#guard Pda.Ascii.wellFormed "vault"
#guard !Pda.Ascii.wellFormed ""
#guard Pda.Ascii.wellFormed (String.ofList (List.replicate 32 'a'))
#guard !Pda.Ascii.wellFormed (String.ofList (List.replicate 33 'a'))
#guard Pda.Ascii.wellFormed "ab\nc"
#guard !Pda.Ascii.wellFormed "λ"

#guard ProofForge.Svm.Ops.Op.wellFormed (.returnU64 (.ext (.findPda "vault") #[]))
#guard !ProofForge.Svm.Ops.Op.wellFormed (.returnU64 (.ext (.findPda "") #[]))
#guard !ProofForge.Svm.Ops.Op.wellFormed
  (.returnU64 (.ext (.findPda (String.ofList (List.replicate 33 'a'))) #[]))
#guard !ProofForge.Svm.Ops.Op.wellFormed
  (.returnU64 (.ext (.checkPda "λ") #[.lit 0]))

#guard Pda.Ascii.bump "vault" == 0
#guard Pda.Ascii.check "vault" == 0
#guard Pda.Ascii.checkBump "vault" 0 == 0
#guard Pda.Ascii.createAccount "vault" 9 16 == 0
#guard System.transfer 7 == 0
#guard System.createAccount 5 16 == 0

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

elab "#pf_guard_svm_pda_system_facades" : command => do
  expectCanonical `Examples.Pda "1f1a994e206aa42b"
  expectCanonical `Examples.Transfer "f2da40e6199ba343"
  expectCanonical `Examples.Create "ae81054e874be24f"
  expectCanonical `Examples.CreatePda "403b2e609334f1ee"

#pf_guard_svm_pda_system_facades

end Tests.SvmSdkPdaSystemSpec
