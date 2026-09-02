import ProofForge
import ProofForge.Evm.Commands
import ProofForge.Wasm.Near.Commands
import Examples.Counter

/-!
# Cross-target Counter conformance (N15 / wsm-near-conformance-001)

`Examples.Counter` is the shared source module for SVM, EVM, and NEAR. Each target
lowers the same entry surface independently; digests differ by design but registry
pins must stay stable. This spec collects the three-target digest table and verifies
build + shared method names in one place.
-/

namespace Tests.CrossTargetCounterSpec

open ProofForge

#guard ProofForge.Svm.Registry.digestOf "Counter" == some "3382e308fa0843e9"
#guard ProofForge.Evm.Registry.digestOf "Counter" == some "254202356ee921d6"
#guard ProofForge.Wasm.Near.Registry.digestOf "Counter" == some "121a0c8f7e697642"

#guard ProofForge.Extract.Legacy.isCounterShape ProofForge.Golden.extractedCounter

open Lean Elab Command

elab "#pf_cross_target_counter_check" : command => do
  let env ← getEnv
  let module := `Examples.Counter
  let svmSource ←
    match Extract.extractModuleIR env module none with
    | .ok source => pure source
    | .error reason => throwError reason
  let svmProgram ←
    match ProofForge.Svm.IR.fromExtracted svmSource with
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
  unless svmDigest == "3382e308fa0843e9" &&
      evmDigest == "254202356ee921d6" &&
      nearDigest == "121a0c8f7e697642" do
    throwError
      s!"cross-target Counter digest mismatch: svm={svmDigest} evm={evmDigest} near={nearDigest}"
  let svmMethods := svmProgram.methods.map (·.ixName) |>.qsort (· < ·)
  let evmMethods :=
    (#[evmProgram.constructor.ixName] ++ evmProgram.entries.map (·.ixName)) |>.qsort (· < ·)
  let nearMethods :=
    (#[nearProgram.initializer.ixName] ++ nearProgram.entries.map (·.ixName)) |>.qsort (· < ·)
  let shared := #["decrement", "divide", "get", "increment", "initialize", "modulo", "nonzero", "scale"]
  unless svmMethods == shared && evmMethods == shared && nearMethods == shared do
    throwError
      s!"Counter method surface diverged:\n  svm={svmMethods}\n  evm={evmMethods}\n  near={nearMethods}"
  logInfo m!"cross-target-counter: svm={svmDigest} evm={evmDigest} near={nearDigest}"

#pf_cross_target_counter_check

#pf_near_build Examples.Counter

#pf_evm_build Examples.Counter

end Tests.CrossTargetCounterSpec
