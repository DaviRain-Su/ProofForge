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

/-- N14: capacity 4 + bare prefix `VEC1` (`0x31434556`). Length stays in `State`. -/
@[pf_inline] def slots : DirectVector64.Handle :=
  DirectVector64.handle 4 (0x31434556 : Prefix4)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { length := 0, marker := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.length

@[pf_entry]
def getAt (state : State) (index : UInt64) : UInt64 :=
  slots.getD state.length index 0

@[pf_entry]
def push (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if slots.canPush state.length then
    let result : ResultBuffer := 8
    let _ := result.write
      (slots.elementKey state.length)
      (slots.elementValue value)
    .ok ({ length := state.length + 1, marker := state.length + 1 }, state.length + 1)
  else
    .error .overflow

@[pf_entry]
def setFirst (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if slots.contains state.length 0 then
    let result : ResultBuffer := 8
    let _ := result.write
      (slots.elementKey 0)
      (slots.elementValue value)
    .ok ({ length := state.length, marker := value }, value)
  else
    .error .overflow

@[pf_entry]
def pop (state : State) : Except Error (State × UInt64) :=
  if slots.contains state.length (state.length - 1) then
    let result : ResultBuffer := 8
    let _ := result.remove (slots.elementKey (state.length - 1))
    .ok ({ length := state.length - 1, marker := state.length - 1 }, state.length - 1)
  else
    .error .overflow

end Examples.NearVector
