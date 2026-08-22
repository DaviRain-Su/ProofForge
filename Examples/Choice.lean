import SolanaLean

namespace Examples.Choice

inductive Pick where
  | empty
  | hold (n : UInt64)
  deriving Repr, DecidableEq, Inhabited

structure State where
  pick : Pick
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { pick := .empty }

@[solana_entry]
def getHeld (s : State) : UInt64 :=
  match s.pick with
  | .empty => 0
  | .hold n => n

/-- `0 ≠ 1` 恒真，给无参 mutate 一条比较守卫。 -/
@[solana_entry]
def setEmpty (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ pick := .empty }, 0)
  else
    .error .overflow

def u64Max : UInt64 := ~~~(0 : UInt64)

@[solana_entry]
def setHold (_s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if n ≤ u64Max then
    .ok ({ pick := .hold n }, n)
  else
    .error .overflow

end Examples.Choice
