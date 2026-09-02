import ProofForge

namespace Examples.Near.NearJsonBooleanMutation
structure State where
  left : UInt64
  right : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init : State := { left := 1, right := 2 }
@[pf_entry] def get (state : State) : UInt64 := state.left
@[pf_entry] def left (state : State) : UInt64 := state.left
@[pf_entry] def right (state : State) : UInt64 := state.right

/-- Mutate two independent fields and return an independently supplied Boolean discriminant. The
target validates the discriminant, so an out-of-range value traps and rolls back both writes. -/
@[pf_entry] def setChecked (_state : State) (result : UInt64) :
    Except Error (State × JsonBooleanResult) :=
  .ok ({ left := 11, right := 22 }, { value := result })

end Examples.Near.NearJsonBooleanMutation