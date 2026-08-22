import Examples.Window

namespace Tests.WindowSpec

open Examples.Window

#guard
  let s := init 7
  s.cells[0] == 7 && s.cells[1] == 0

#guard getHead (init 7) == 7

#guard
  match setTail (init 7) 9 with
  | .ok (st, ret) => st.cells[0] == 7 && st.cells[1] == 9 && ret == 9
  | .error _ => false

#guard
  match ProofForge.IR.fieldOffset ProofForge.Golden.extractedWindow "cells_1" with
  | some 16 => true
  | _ => false

#guard ProofForge.IR.dataLen ProofForge.Golden.extractedWindow == 24

end Tests.WindowSpec
