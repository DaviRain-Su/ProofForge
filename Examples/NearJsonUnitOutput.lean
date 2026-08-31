import ProofForge

namespace Examples.NearJsonUnitOutput

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init : State := { marker := 0 }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-- Explicit logical Unit result for NEAR's default JSON mutating return codec. -/
@[pf_entry] def setMarker (_state : State) (marker : UInt64) : Except Error (State × Unit) :=
  if marker != 0 then .ok ({ marker }, ()) else .error .overflow

end Examples.NearJsonUnitOutput
