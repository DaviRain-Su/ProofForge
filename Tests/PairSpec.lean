import Examples.Pair

namespace Tests.PairSpec

open Examples.Pair

#guard
  match creditLeft (init 5) 3 with
  | .ok (st, ret) => st.left == 8 && st.right == 0 && ret == 8
  | .error _ => false

#guard
  match creditLeft { left := 5, right := 99 } 3 with
  | .ok (st, ret) => st.left == 8 && st.right == 99 && ret == 8
  | .error _ => false

#guard
  match creditLeft { left := u64Max, right := 1 } 1 with
  | .error .overflow => true
  | .ok _ => false

#guard getLeft (init 7) == 7

end Tests.PairSpec
