import SolanaLean

namespace Examples.Window

structure State where
  cells : Vector UInt64 2
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[solana_entry]
def init (first : UInt64) : State :=
  { cells := #v[first, 0] }

@[solana_entry]
def getHead (s : State) : UInt64 :=
  s.cells[0]

/-- 只改第二格，第一格保持。 -/
@[solana_entry]
def setTail (s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if n ≤ u64Max then
    .ok ({ cells := s.cells.set 1 n }, n)
  else
    .error .overflow

end Examples.Window
