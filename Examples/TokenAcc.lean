import ProofForge

namespace Examples.TokenAcc

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

/-- Token InitializeAccount3；owner = 账户 0。 -/
@[pf_entry]
def openAcc (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenInitAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

/-- Token CloseAccount；lamports 退回账户 2。 -/
@[pf_entry]
def closeAcc (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenCloseAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenAcc
