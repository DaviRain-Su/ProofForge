import ProofForge

namespace Examples.Phase

inductive Mode where
  | idle
  | live
  deriving Repr, DecidableEq, Inhabited

structure State where
  mode : Mode
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { mode := .idle }

@[pf_entry]
def isLive (s : State) : UInt64 :=
  if s.mode = .live then 1 else 0

/-- `0 ≠ 1` 恒真，给无参 mutate 一条比较守卫。 -/
@[pf_entry]
def setIdle (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ mode := .idle }, 0)
  else
    .error .overflow

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def setLive (_s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if n ≤ u64Max then
    .ok ({ mode := .live }, 1)
  else
    .error .overflow

end Examples.Phase
