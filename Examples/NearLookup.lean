import ProofForge

namespace Examples.NearLookup

open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def mapGet (_state : State) (key : UInt64) : UInt64 :=
  (0x3150414d : DirectLookupMap64).getD key 0

@[pf_entry]
def mapHas (_state : State) (key : UInt64) : UInt64 :=
  (0x3150414d : DirectLookupMap64).has key

@[pf_entry]
def mapPut (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let status := (0x3150414d : DirectLookupMap64).put 7 value
  .ok ({ marker := status }, status)

@[pf_entry]
def mapRemove (_state : State) : Except Error (State × UInt64) :=
  let status := (0x3150414d : DirectLookupMap64).remove 7
  .ok ({ marker := status }, status)

@[pf_entry]
def setHas (_state : State) (value : UInt64) : UInt64 :=
  (0x31544553 : DirectLookupSet64).has value

@[pf_entry]
def setInsert (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let inserted := (0x31544553 : DirectLookupSet64).insert value
  .ok ({ marker := inserted }, inserted)

@[pf_entry]
def setRemove (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let removed := (0x31544553 : DirectLookupSet64).remove value
  .ok ({ marker := removed }, removed)

end Examples.NearLookup
