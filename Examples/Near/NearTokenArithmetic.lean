import ProofForge

namespace Examples.Near.NearTokenArithmetic
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

@[pf_entry] def mulFactorZeroOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨7, 9⟩ 0 then 1 else 0
@[pf_entry] def mulFactorZeroW0 (_state : State) : UInt64 := NearToken.mulUInt64W0 ⟨7, 9⟩ 0
@[pf_entry] def mulFactorZeroW1 (_state : State) : UInt64 := NearToken.mulUInt64W1 ⟨7, 9⟩ 0

@[pf_entry] def mulTokenZeroOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0, 0⟩ 0xffffffffffffffff then 1 else 0
@[pf_entry] def mulTokenZeroW0 (_state : State) : UInt64 :=
  NearToken.mulUInt64W0 ⟨0, 0⟩ 0xffffffffffffffff
@[pf_entry] def mulTokenZeroW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨0, 0⟩ 0xffffffffffffffff

@[pf_entry] def mulMixedOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨1, 1⟩ 2 then 1 else 0
@[pf_entry] def mulMixedW0 (_state : State) : UInt64 := NearToken.mulUInt64W0 ⟨1, 1⟩ 2
@[pf_entry] def mulMixedW1 (_state : State) : UInt64 := NearToken.mulUInt64W1 ⟨1, 1⟩ 2

@[pf_entry] def mulU64SquareOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0xffffffffffffffff, 0⟩ 0xffffffffffffffff then 1 else 0
@[pf_entry] def mulU64SquareW0 (_state : State) : UInt64 :=
  NearToken.mulUInt64W0 ⟨0xffffffffffffffff, 0⟩ 0xffffffffffffffff
@[pf_entry] def mulU64SquareW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨0xffffffffffffffff, 0⟩ 0xffffffffffffffff

@[pf_entry] def mulMaxOneOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ 1 then 1 else 0
@[pf_entry] def mulMaxOneW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ 1
@[pf_entry] def mulMaxTwoOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ 2 then 1 else 0

@[pf_entry] def mulHighFitOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0, 1⟩ 0xffffffffffffffff then 1 else 0
@[pf_entry] def mulHighFitW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨0, 1⟩ 0xffffffffffffffff
@[pf_entry] def mulExactMaxOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨1, 1⟩ 0xffffffffffffffff then 1 else 0
@[pf_entry] def mulExactMaxW0 (_state : State) : UInt64 :=
  NearToken.mulUInt64W0 ⟨1, 1⟩ 0xffffffffffffffff
@[pf_entry] def mulExactMaxW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨1, 1⟩ 0xffffffffffffffff

/-- `hi*m` fits one limb, but adding the low product's high limb overflows. -/
@[pf_entry] def mulCarryOverflowOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0xffffffffffffffff, 1⟩ 0xffffffffffffffff then 1 else 0

/-- Largest successful high result limb through the cross-product addition path. -/
@[pf_entry] def mulCarryBoundaryOk (_state : State) : UInt64 :=
  if NearToken.canMulUInt64 ⟨0xffffffffffffffff, 0xffffffff⟩ 0x100000000 then 1 else 0
@[pf_entry] def mulCarryBoundaryW0 (_state : State) : UInt64 :=
  NearToken.mulUInt64W0 ⟨0xffffffffffffffff, 0xffffffff⟩ 0x100000000
@[pf_entry] def mulCarryBoundaryW1 (_state : State) : UInt64 :=
  NearToken.mulUInt64W1 ⟨0xffffffffffffffff, 0xffffffff⟩ 0x100000000

end Examples.Near.NearTokenArithmetic