import Examples.Token2022

namespace Tests.Token2022Spec

open Lean Elab Command
open Examples.Token2022
open ProofForge.Svm
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard token2022TransferChecked 7 6 == 0

#guard
  match send (init 0) 9 with
  | .ok (state, returned) => state.dummy == 0 && returned == 9
  | .error _ => false

elab "#pf_guard_token_2022_ir" : command => do
  let env ← getEnv
  let extracted ←
    match ProofForge.Extract.extractModuleIR env `Examples.Token2022 with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted extracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sendMethod := program.methods.find? (·.ixName == "send")
    | throwError "missing Token2022 send method"
  let expectedInvoke : IR.Op :=
    .invoke 4
      #[{ acc := 1, writable := true, expectedDataLen := some 165 },
        { acc := 2, expectedDataLen := some 82 },
        { acc := 3, writable := true, expectedDataLen := some 165 },
        { acc := 0, signer := true }]
      #[.u8le (.lit 12), .u64le (.arg 0), .u8le (.lit 6)] #[] none
  unless sendMethod.ops.contains expectedInvoke do
    throwError s!"Token-2022 constrained CPI was not retained: {repr sendMethod.ops}"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "; validate statically constrained CPI account data lengths" &&
      asm.contains "jne r1, 165, cpi_data_len_err_" &&
      asm.contains "jne r1, 82, cpi_data_len_err_" &&
      asm.contains "call sol_invoke_signed_c" do
    throwError "Token-2022 exact account-length preflight is missing from assembly"

#pf_guard_token_2022_ir

#guard ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 1, expectedDataLen := some 165 }

#guard !ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 1, expectedDataLen := some 18446744073709551616 }

end Tests.Token2022Spec
