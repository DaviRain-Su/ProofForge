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
#guard Pda.Ascii.createRentExempt "vault" 16 == 0
#guard System.transfer 7 == 0
#guard System.createAccount 5 16 == 0
#guard System.createRentExempt 16 == 0

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

private def hasRentAwareCreate (program : ProofForge.Svm.IR.Program)
    (methodName : String) : Bool :=
  match program.methods.find? (·.ixName == methodName) with
  | none => false
  | some method => method.ops.any fun
      | .invoke _ _ data _ _ =>
          data.any fun
            | .u64le (.ext (.rentExemption 16) #[]) => true
            | _ => false
      | _ => false

private def extractModule (env : Environment) (module : Name) :
    Except String ProofForge.Svm.IR.Program := do
  let source ← ProofForge.Extract.extractModuleIR env module
  ProofForge.Svm.IR.fromExtracted source

elab "#pf_guard_svm_pda_system_facades" : command => do
  expectCanonical `Examples.Pda "1f1a994e206aa42b"
  expectCanonical `Examples.Transfer "f2da40e6199ba343"
  expectCanonical `Examples.Create "6ee1719e05c53163"
  expectCanonical `Examples.CreatePda "ef405b71cc52f3ec"
  let env ← getEnv
  let create ←
    match extractModule env `Examples.Create with
    | .ok program => pure program
    | .error reason => throwError reason
  let createPda ←
    match extractModule env `Examples.CreatePda with
    | .ok program => pure program
    | .error reason => throwError reason
  unless hasRentAwareCreate create "createRentExempt" &&
      hasRentAwareCreate createPda "openRentExempt" do
    throwError "rent-aware System/PDA facade lost the existing Rent query inside CreateAccount"

#pf_guard_svm_pda_system_facades

end Tests.SvmSdkPdaSystemSpec
