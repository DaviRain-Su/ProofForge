import SolanaLean

namespace Examples.Pair

structure State where
  left : UInt64
  right : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[solana_entry]
def init (left : UInt64) : State :=
  { left, right := 0 }

@[solana_entry]
def getLeft (s : State) : UInt64 :=
  s.left

/-- 只改 `left`，`right` 保持。 -/
@[solana_entry]
def creditLeft (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.left ≤ u64Max - delta then
    let next := s.left + delta
    .ok ({ left := next, right := s.right }, next)
  else
    .error .overflow

theorem creditLeft_overflow_not_ok
    (s : State) (d : UInt64)
    (h : creditLeft s d = .error .overflow) :
    ¬ ∃ t r, creditLeft s d = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

end Examples.Pair
