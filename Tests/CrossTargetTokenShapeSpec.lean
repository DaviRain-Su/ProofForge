import ProofForge
import ProofForge.Svm.Commands
import ProofForge.Evm.Commands
import ProofForge.Wasm.Near.Commands
import Examples.TokenShape

/-!
# Cross-target TokenShape conformance (N15 shared transfer stub)

`Examples.TokenShape` is the shared Lean source for the **transfer-shaped** UInt64 subset
that SVM, EVM, and NEAR can all lower (`initialize` / `get` / `credit` / `debit`). Digests
differ by target and are pinned below. Approve/allowance stays target-local (NEAR NEP-141 has
no approve).
-/

namespace Tests.CrossTargetTokenShapeSpec

open ProofForge

#guard ProofForge.Svm.Registry.digestOf "TokenShape" == some "d9f1c090ffa3b9d"
#guard ProofForge.Evm.Registry.digestOf "TokenShape" == some "2517523f63989d26"
#guard ProofForge.Wasm.Near.Registry.digestOf "TokenShape" == some "f824063d978669c6"

open Lean Elab Command

elab "#pf_cross_target_token_shape_check" : command => do
  let env ← getEnv
  let module := `Examples.TokenShape
  let svmProgram ←
    match Extract.extractModuleIR env module none >>= ProofForge.Svm.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let evmProgram ←
    match Extract.extractModuleIR env module none >>= ProofForge.Evm.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let nearProgram ←
    match Extract.extractModuleIR env module none >>= ProofForge.Wasm.Near.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmDigest := ProofForge.Svm.IR.digestHex svmProgram
  let evmDigest := ProofForge.Evm.IR.digestHex evmProgram
  let nearDigest := ProofForge.Wasm.Near.IR.digestHex nearProgram
  unless svmDigest == "d9f1c090ffa3b9d" &&
      evmDigest == "2517523f63989d26" &&
      nearDigest == "f824063d978669c6" do
    throwError
      s!"TokenShape digest mismatch: svm={svmDigest} evm={evmDigest} near={nearDigest}"
  let shared := #["credit", "debit", "get", "initialize"]
  let svmMethods := svmProgram.methods.map (·.ixName) |>.qsort (· < ·)
  let evmMethods :=
    (#[evmProgram.constructor.ixName] ++ evmProgram.entries.map (·.ixName)) |>.qsort (· < ·)
  let nearMethods :=
    (#[nearProgram.initializer.ixName] ++ nearProgram.entries.map (·.ixName)) |>.qsort (· < ·)
  unless svmMethods == shared && evmMethods == shared && nearMethods == shared do
    throwError
      s!"TokenShape method surface diverged:\n  svm={svmMethods}\n  evm={evmMethods}\n  near={nearMethods}"
  logInfo m!"cross-target-token-shape: svm={svmDigest} evm={evmDigest} near={nearDigest}"

#pf_cross_target_token_shape_check

#pf_build Examples.TokenShape
#pf_evm_build Examples.TokenShape
#pf_near_build Examples.TokenShape

end Tests.CrossTargetTokenShapeSpec
