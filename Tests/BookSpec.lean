import Examples.Svm.Book
import ProofForge

namespace Tests.BookSpec

open Examples.Svm.Book

#guard (init 7).cells[0]! == 7
#guard get (init 7) == 7
#guard getAt (init 7) 0 == 7
#guard getAt (init 7) 9 == 0

#guard
  match setAt (init 7) 1 9 with
  | .ok (st, ret) => st.cells[1]! == 9 && ret == 9 && st.cells[0]! == 7
  | .error _ => false

#guard
  match setAt (init 7) 9 1 with
  | .error .overflow => true
  | _ => false

#guard
  match fillFirst (init 7) 3 with
  | .ok (st, ret) => st.cells[1]! == 3 && ret == 3 && st.cells[0]! == 7
  | .error _ => false

#guard
  match fillFirst { cells := #v[1, 1, 1, 1] } 3 with
  | .error .overflow => true
  | _ => false

#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedBook == 40

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedBook with
  | .error _ => false
  | .ok asm =>
      match asm.splitOn "body_setAt:" with
      | _ :: body :: _ =>
          let body := (body.splitOn "\nget:")[0]!
          body.contains "; indexSet cells[4]+0" &&
            !body.contains "stxdw [r6 + ACC0_DATA + 8], r1"
      | _ => false

end Tests.BookSpec
