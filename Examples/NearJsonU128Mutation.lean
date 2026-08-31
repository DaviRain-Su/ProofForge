import ProofForge

namespace Examples.NearJsonU128Mutation

open ProofForge.Core.Value

structure State where
  left : UInt64
  right : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init : State := { left := 0, right := 0 }
@[pf_entry] def get (state : State) : UInt64 := state.left
@[pf_entry] def right (state : State) : UInt64 := state.right

/-- Fixture for state persistence followed by an independent asymmetric quoted-u128 result. -/
@[pf_entry]
def commitAsymmetric (_state : State) (next : UInt64) : Except Error (State × UInt128) :=
  if next != 0 then
    .ok ({ left := next, right := 0x8877665544332211 }, ⟨2, 1⟩)
  else
    .error .overflow

end Examples.NearJsonU128Mutation
