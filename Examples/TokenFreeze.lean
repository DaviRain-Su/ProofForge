import SolanaLean

namespace Examples.TokenFreeze

open SolanaLean.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- Token FreezeAccount。 -/
@[solana_entry]
def freeze (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenFreezeAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

/-- Token ThawAccount。 -/
@[solana_entry]
def thaw (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenThawAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenFreeze
