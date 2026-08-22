import SolanaLean

namespace Examples.TokenSize

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

/-- Token GetAccountDataSize；返回值走 `cpiReturn`。 -/
@[solana_entry]
def size (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let n := tokenAccountSize
    .ok ({ dummy := 0 }, n)
  else
    .error .overflow

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenSize
