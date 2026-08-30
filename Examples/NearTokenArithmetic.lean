import ProofForge

namespace Examples.NearTokenArithmetic

open ProofForge.Wasm.Near.Sdk

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State := ⟨0⟩

@[pf_entry]
def get (state : State) : UInt64 := state.marker

@[pf_entry]
def touch (state : State) (delta : UInt64) : Except Error (State × UInt64) :=
  let next := state.marker + delta
  if next ≥ state.marker then .ok (⟨next⟩, next) else .error .overflow

@[pf_entry]
def addCarryOk (_state : State) : UInt64 :=
  if NearToken.canAdd ⟨0xffffffffffffffff, 0⟩ ⟨1, 0⟩ then 1 else 0

@[pf_entry]
def addCarryW0 (_state : State) : UInt64 :=
  NearToken.addW0 ⟨0xffffffffffffffff, 0⟩ ⟨1, 0⟩

@[pf_entry]
def addCarryW1 (_state : State) : UInt64 :=
  NearToken.addW1 ⟨0xffffffffffffffff, 0⟩ ⟨1, 0⟩

@[pf_entry]
def addOverflowOk (_state : State) : UInt64 :=
  if NearToken.canAdd ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ ⟨1, 0⟩ then 1 else 0

@[pf_entry]
def addOverflowW0 (_state : State) : UInt64 :=
  NearToken.addW0 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ ⟨1, 0⟩

@[pf_entry]
def addOverflowW1 (_state : State) : UInt64 :=
  NearToken.addW1 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ ⟨1, 0⟩

@[pf_entry]
def addHighOk (_state : State) : UInt64 :=
  if NearToken.canAdd ⟨0, 0x8000000000000000⟩ ⟨1, 0x7ffffffffffffffe⟩ then 1 else 0

@[pf_entry]
def addHighW1 (_state : State) : UInt64 :=
  NearToken.addW1 ⟨0, 0x8000000000000000⟩ ⟨1, 0x7ffffffffffffffe⟩

@[pf_entry]
def subBorrowOk (_state : State) : UInt64 :=
  if NearToken.canSub ⟨0, 1⟩ ⟨1, 0⟩ then 1 else 0

@[pf_entry]
def subBorrowW0 (_state : State) : UInt64 :=
  NearToken.subW0 ⟨0, 1⟩ ⟨1, 0⟩

@[pf_entry]
def subBorrowW1 (_state : State) : UInt64 :=
  NearToken.subW1 ⟨0, 1⟩ ⟨1, 0⟩

@[pf_entry]
def subUnderflowOk (_state : State) : UInt64 :=
  if NearToken.canSub ⟨0, 0⟩ ⟨1, 0⟩ then 1 else 0

@[pf_entry]
def subUnderflowW0 (_state : State) : UInt64 :=
  NearToken.subW0 ⟨0, 0⟩ ⟨1, 0⟩

@[pf_entry]
def subUnderflowW1 (_state : State) : UInt64 :=
  NearToken.subW1 ⟨0, 0⟩ ⟨1, 0⟩

@[pf_entry]
def subHighOk (_state : State) : UInt64 :=
  if NearToken.canSub ⟨0, 0x8000000000000000⟩ ⟨0, 0x7fffffffffffffff⟩ then 1 else 0

@[pf_entry]
def subHighW1 (_state : State) : UInt64 :=
  NearToken.subW1 ⟨0, 0x8000000000000000⟩ ⟨0, 0x7fffffffffffffff⟩

end Examples.NearTokenArithmetic
