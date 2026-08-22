import ProofForge

namespace Examples.TokenMint

open ProofForge.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- Token MintToChecked；decimals 钉死为 6。 -/
@[pf_entry]
def mintTo (_s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenMintToChecked amount 6
    .ok ({ dummy := 0 }, amount)
  else
    .error .overflow

/-- Token BurnChecked；decimals 钉死为 6。 -/
@[pf_entry]
def burn (_s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenBurnChecked amount 6
    .ok ({ dummy := 0 }, amount)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenMint
