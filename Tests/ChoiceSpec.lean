import Examples.Choice

namespace Tests.ChoiceSpec

open Examples.Choice

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
  match SolanaLean.IR.fieldOffset SolanaLean.Golden.extractedChoice "pick_p0" with
  | some 16 => true
  | _ => false

#guard SolanaLean.IR.dataLen SolanaLean.Golden.extractedChoice == 24

end Tests.ChoiceSpec
