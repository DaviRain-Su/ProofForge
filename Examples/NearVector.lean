import ProofForge

namespace Examples.NearVector

open ProofForge.Wasm.Near.Sdk.Store
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  length : UInt64
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { length := 0, marker := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.length

@[pf_entry]
def getAt (state : State) (index : UInt64) : UInt64 :=
  (4 : DirectVector64).getD (0x31434556 : Prefix4) state.length index 0

@[pf_entry]
def push (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if (4 : DirectVector64).canPush state.length then
    let result : ResultBuffer := 8
    let _ := result.write
      ((4 : DirectVector64).elementKey (0x31434556 : Prefix4) state.length)
      ((4 : DirectVector64).elementValue value)
    .ok ({ length := state.length + 1, marker := state.length + 1 }, state.length + 1)
  else
    .error .overflow

@[pf_entry]
def setFirst (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if (4 : DirectVector64).contains state.length 0 then
    let result : ResultBuffer := 8
    let _ := result.write
      ((4 : DirectVector64).elementKey (0x31434556 : Prefix4) 0)
      ((4 : DirectVector64).elementValue value)
    .ok ({ length := state.length, marker := value }, value)
  else
    .error .overflow

@[pf_entry]
def pop (state : State) : Except Error (State × UInt64) :=
  if (4 : DirectVector64).contains state.length (state.length - 1) then
    let result : ResultBuffer := 8
    let _ := result.remove
      ((4 : DirectVector64).elementKey (0x31434556 : Prefix4) (state.length - 1))
    .ok ({ length := state.length - 1, marker := state.length - 1 }, state.length - 1)
  else
    .error .overflow

end Examples.NearVector
