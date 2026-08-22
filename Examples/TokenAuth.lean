import ProofForge

namespace Examples.TokenAuth

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

/-- Token SetAuthority(MintTokens)；新 authority = 账户 2。 -/
@[pf_entry]
def setAuth (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenSetMintAuthority
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

/-- Token Revoke；清掉 source 的 delegate。 -/
@[pf_entry]
def revoke (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenRevoke
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TokenAuth
