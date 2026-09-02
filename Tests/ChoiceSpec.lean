import Examples.Svm.Choice

namespace Tests.ChoiceSpec

open Examples.Svm.Choice

#guard (init 0).pick == .empty
#guard getHeld (init 0) == 0

#guard
  match setHold (init 0) 77 with
  | .ok (st, ret) => st.pick == .hold 77 && ret == 77 && getHeld st == 77
  | .error _ => false

#guard
  match setEmpty { pick := .hold 77 } with
  | .ok (st, ret) => st.pick == .empty && ret == 0 && getHeld st == 0
  | .error _ => false

#guard
  match ProofForge.Svm.ABI.fieldOffset ProofForge.Golden.extractedChoice "pick_p0" with
  | some 16 => true
  | _ => false

#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedChoice == 24

end Tests.ChoiceSpec
