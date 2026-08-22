import Examples.Phase

namespace Tests.PhaseSpec

open Examples.Phase

#guard (init 0).mode == .idle
#guard isLive (init 0) == 0

#guard
  match setLive (init 0) 1 with
  | .ok (st, ret) => st.mode == .live && ret == 1 && isLive st == 1
  | .error _ => false

#guard
  match setIdle { mode := .live } with
  | .ok (st, ret) => st.mode == .idle && ret == 0 && isLive st == 0
  | .error _ => false

#guard
  match ProofForge.IR.fieldOffset ProofForge.Golden.extractedPhase "mode" with
  | some 8 => true
  | _ => false

#guard ProofForge.IR.dataLen ProofForge.Golden.extractedPhase == 16

end Tests.PhaseSpec
