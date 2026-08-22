import SolanaLean

namespace Examples.Decrement

open SolanaLean.Counter

/-- `delta ≤ s.value` 才减，否则 overflow。与 increment 共用抽出/发射。 -/
def decrement (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if delta ≤ s.value then
    let next := s.value - delta
    .ok ({ value := next }, next)
  else
    .error .overflow

theorem decrement_underflow_not_ok
    (s : State) (d : UInt64)
    (h : decrement s d = .error .overflow) :
    ¬ ∃ t r, decrement s d = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

end Examples.Decrement
