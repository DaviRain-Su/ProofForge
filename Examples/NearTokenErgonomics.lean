import ProofForge

namespace Examples.NearTokenErgonomics

open ProofForge.Wasm.Near.Sdk
open ProofForge.Core.Except

private def u64Max : UInt64 := ~~~(0 : UInt64)

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init : State := ⟨0⟩
@[pf_entry] def get (state : State) : UInt64 := state.marker

@[pf_entry]
def touch (state : State) (delta : UInt64) : Except Error (State × UInt64) :=
  let next := state.marker + delta
  if next ≥ state.marker then .ok (⟨next⟩, next) else .error .overflow

private def checkedAdd (a b : UInt64) : Except Error UInt64 :=
  if a ≤ u64Max - b then ok (a + b) else err .overflow

attribute [pf_inline] checkedAdd

/-- Fallible scalar chain via `Core.Except.andThen` (not `do` notation). -/
@[pf_entry]
def addViaAndThen (state : State) (delta : UInt64) : Except Error (State × UInt64) :=
  andThen (checkedAdd state.marker delta) fun sum =>
    ok (⟨sum⟩, sum)

@[pf_entry]
def canAddViaHelper (_state : State) : UInt64 :=
  if NearToken.canAdd ⟨1, 0⟩ ⟨2, 0⟩ then 1 else 0

@[pf_entry]
def addViaHelperW0 (_state : State) : UInt64 :=
  NearToken.addW0 ⟨1, 0⟩ ⟨2, 0⟩

end Examples.NearTokenErgonomics
