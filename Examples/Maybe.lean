import ProofForge

namespace Examples.Maybe

structure State where
  slot : Option UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { slot := none }

@[pf_entry]
def isSome (s : State) : UInt64 :=
  if s.slot.isSome then 1 else 0

@[pf_entry]
def getValue (s : State) : UInt64 :=
  match s.slot with
  | none => 0
  | some n => n

/-- `0 ≠ 1` 恒真，给无参 mutate 一条比较守卫（不是 checked 算术）。 -/
@[pf_entry]
def setNone (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ slot := none }, 0)
  else
    .error .overflow

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def setSome (_s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if n ≤ u64Max then
    .ok ({ slot := some n }, n)
  else
    .error .overflow

end Examples.Maybe
