import ProofForge

namespace Examples.TokenMint2

open ProofForge.Svm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- Token InitializeMint2；decimals 钉死 6，authority = 账户 0。 -/
@[pf_entry]
def openMint (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenInitMint
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenMint2
