import ProofForge

namespace Examples.Svm.Token2022MintClose

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

/--
Token-2022 `TransferChecked` that permits a mint carrying exactly one official
`MintCloseAuthority` extension. Decimals are fixed at 6.
-/
@[pf_entry]
def send (_state : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := token2022TransferCheckedMintClose amount 6
    .ok ({ dummy := 0 }, amount)
  else
    .error .overflow

@[pf_entry]
def get (_state : State) : UInt64 :=
  0

end Examples.Svm.Token2022MintClose
