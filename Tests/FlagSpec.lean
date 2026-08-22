import Examples.Flag
import Examples.Maybe

namespace Tests.FlagSpec

open Examples.Flag

#guard
  let s := init 7
  s.flag == 0 && s.count == 7

#guard getFlag (init 7) == 0

#guard
  match setFlag (init 7) 1 with
  | .ok (st, ret) => st.flag == 1 && st.count == 7 && ret == 1
  | .error _ => false

#guard
  match setFlag (init 7) 256 with
  | .error .overflow => true
  | .ok _ => false

end Tests.FlagSpec

namespace Tests.MaybeSpec

open Examples.Maybe

#guard (init 0).slot == none

#guard isSome (init 0) == 0

#guard
  match setSome (init 0) 77 with
  | .ok (st, ret) => st.slot == some 77 && ret == 77 && isSome st == 1
  | .error _ => false

#guard
  match setNone { slot := some 77 } with
  | .ok (st, ret) => st.slot == none && ret == 0 && isSome st == 0
  | .error _ => false

#guard getValue (init 0) == 0
#guard
  match setSome (init 0) 77 with
  | .ok (st, _) => getValue st == 77
  | .error _ => false

end Tests.MaybeSpec
