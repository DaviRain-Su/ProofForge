import ProofForge

namespace Examples.Token2022

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

/-- Token-2022 base-layout `TransferChecked`; decimals are fixed at 6. -/
@[pf_entry]
def send (_state : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := token2022TransferChecked amount 6
    .ok ({ dummy := 0 }, amount)
  else
    .error .overflow

@[pf_entry]
def get (_state : State) : UInt64 :=
  0

end Examples.Token2022
