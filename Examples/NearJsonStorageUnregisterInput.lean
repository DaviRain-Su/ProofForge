import ProofForge

namespace Examples.NearJsonStorageUnregisterInput

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Parser diagnostics only. This fixture does not unregister accounts or export
`storage_unregister`. -/
@[pf_entry] def inspectForce (_state : State) (args : StorageUnregisterArgs) : UInt64 :=
  args.force

@[pf_entry] def commitForce (_state : State) (args : StorageUnregisterArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.force }, args.force)

end Examples.NearJsonStorageUnregisterInput
