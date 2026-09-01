import Examples.TransientPubkeyBatch
import Examples.TransientPubkeyRing
import Lean
import ProofForge

/-!
Focused geometry and extraction checks for svm-sdk-003 typed Pubkey transient vectors.
-/

namespace Tests.SvmTransientPubkeyVectorSpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk.Transient

private def batch3 := VectorPubkey.bounded 3
private def batch2Alt := VectorPubkey.boundedAlt 2
private def ring2 := VectorPubkey.bounded 2
private def ringEdgeAlt := VectorPubkey.boundedAlt 1023

#guard batch3.wellFormed
#guard batch2Alt.wellFormed
#guard ring2.wellFormed
#guard ringEdgeAlt.wellFormed
#guard !(VectorPubkey.bounded 0).wellFormed
#guard !(VectorPubkey.boundedAlt 1024).wellFormed
#guard batch3 == { elements := 3, alternate := false }
#guard batch2Alt == { elements := 2, alternate := true }

#pf_build Examples.TransientPubkeyBatch
#pf_build Examples.TransientPubkeyRing

elab "#pf_guard_transient_pubkey_vectors" : command => do
  let env ← getEnv
  let extract (moduleName : Name) : CommandElabM IR.Program := do
    let source ←
      match ProofForge.Extract.extractModuleIR env moduleName with
      | .ok source => pure source
      | .error reason => throwError reason
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let batch ← extract `Examples.TransientPubkeyBatch
  let ring ← extract `Examples.TransientPubkeyRing
  let some pushExact := batch.methods.find? (·.ixName == "pushExact")
    | throwError "missing TransientPubkeyBatch.pushExact"
  unless pushExact.paramCount == 4 do
    throwError "pushExact should accept four Pubkey limbs"
  let some clearWhenFull := ring.methods.find? (·.ixName == "clearWhenFull")
    | throwError "missing TransientPubkeyRing.clearWhenFull"
  unless clearWhenFull.paramCount == 4 do
    throwError "clearWhenFull should accept four Pubkey limbs"
  -- Returning a Pubkey materializes four scalar limbs on the managed result frame.
  unless pushExact.retCount == 4 && clearWhenFull.retCount == 4 do
    throwError "Pubkey returns must expose four limb slots"

#pf_guard_transient_pubkey_vectors

end Tests.SvmTransientPubkeyVectorSpec
