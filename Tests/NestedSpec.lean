import Examples.Nested
import ProofForge

namespace Tests.NestedSpec

open Examples.Nested

#guard (init 100).book.price == 100
#guard (init 100).book.size == 0
#guard bestAsk (init 100) == 100
#guard askSize (init 100) == 0

#guard
  match postAsk (init 100) 8 with
  | .ok (st, ret) => st.book.size == 8 && ret == 8 && st.book.price == 100
  | .error _ => false

#guard
  match postAsk { book := { price := 100, size := u64Max }, baseFree := 0 } 1 with
  | .error .overflow => true
  | _ => false

#guard ProofForge.Golden.extractedNested.fields == #["book_price", "book_size", "baseFree"]
#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedNested == 32

end Tests.NestedSpec
