import ProofForge

namespace Examples.NearJsonMessageInput

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Codec diagnostics only; these are not public FT methods. -/
@[pf_entry] def messageLength (_state : State) (msg : BoundedMessage64) : UInt64 := msg.length
@[pf_entry] def messageW0 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w0
@[pf_entry] def messageW1 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w1
@[pf_entry] def messageW2 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w2
@[pf_entry] def messageW3 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w3
@[pf_entry] def messageW4 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w4
@[pf_entry] def messageW5 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w5
@[pf_entry] def messageW6 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w6
@[pf_entry] def messageW7 (_state : State) (msg : BoundedMessage64) : UInt64 := msg.w7
@[pf_entry] def commitLength (_state : State) (msg : BoundedMessage64) : Except Error (State × UInt64) :=
  .ok ({ marker := msg.length }, msg.length)

end Examples.NearJsonMessageInput
