import ProofForge

namespace Examples.Near.NearJsonAmountInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Core.Value

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

/-! These methods exercise the compiler-owned canonical quoted-u128 amount object input.
They are codec fixtures, not public NEP-141 methods or a generic JSON ABI. -/

@[pf_entry]
def amountW0 (_state : State) (amount : UInt128) : UInt64 :=
  amount.w0

@[pf_entry]
def amountW1 (_state : State) (amount : UInt128) : UInt64 :=
  amount.w1

@[pf_entry]
def commitW1 (_state : State) (amount : UInt128) : Except Error (State × UInt64) :=
  .ok ({ marker := amount.w1 }, amount.w1)

end Examples.Near.NearJsonAmountInput