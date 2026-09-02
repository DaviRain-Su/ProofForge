import ProofForge

namespace Examples.NearQueue

open ProofForge.Wasm.Near.Sdk.Store
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  head : UInt64
  length : UInt64
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- N14 Queue Handle: capacity 3 + bare prefix `QUE1` (`0x31455551`). Head/length stay in `State`. -/
@[pf_inline] def slots : DirectQueue64.Handle :=
  DirectQueue64.handle 3 (0x31455551 : Prefix4)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { head := 0, length := 0, marker := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.length

@[pf_entry]
def getHead (state : State) : UInt64 :=
  state.head

@[pf_entry]
def getAt (state : State) (offset : UInt64) : UInt64 :=
  slots.getD state.head state.length offset 0

@[pf_entry]
def hasAt (state : State) (offset : UInt64) : UInt64 :=
  slots.hasOffset state.head state.length offset

@[pf_entry]
def peek (state : State) : UInt64 :=
  slots.getD state.head state.length 0 0

@[pf_entry]
def push (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if slots.canPush state.head state.length then
    let index := slots.physicalIndex state.head state.length
    let result : ResultBuffer := 8
    let _ := result.write
      (slots.elementKey index)
      (slots.elementValue value)
    .ok ({ state with length := state.length + 1, marker := state.length + 1 }, state.length + 1)
  else
    .error .overflow

@[pf_entry]
def pop (state : State) : Except Error (State × UInt64) :=
  if slots.offsetInRange state.head state.length 0 then
    if state.length = 1 then
      let index := slots.physicalIndex state.head 0
      let result : ResultBuffer := 8
      let _ := result.remove (slots.elementKey index)
      .ok ({ head := 0, length := 0, marker := 0 }, 0)
    else
      let index := slots.physicalIndex state.head 0
      let result : ResultBuffer := 8
      let _ := result.remove (slots.elementKey index)
      .ok ({
        head := slots.nextHead state.head
        length := state.length - 1
        marker := state.length - 1
      }, state.length - 1)
  else
    .error .overflow

/-- Deliberately create malformed metadata for the fail-closed sandbox scene. -/
@[pf_entry]
def malform (_state : State) : Except Error (State × UInt64) :=
  .ok ({ head := 3, length := 1, marker := 99 }, 99)

end Examples.NearQueue
