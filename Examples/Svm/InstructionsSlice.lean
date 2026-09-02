import ProofForge

/-!
Independent consumer for svm-rt-004: bounded Instructions sysvar + fixed-offset sliced reads.

Physical account 0 is ProofForge state; account 1 is the Instructions sysvar (or a fixture with
the same key/layout). Compile-time geometry is a 24-byte serialized blob:

* `u16` `num_instructions` at offset 0
* marker `u64` at offset 8 (slice window)
* `u16` `current_index` at offset 16 (low half of word 2; bytes 18..23 pad the
  compile-time 24-byte window so end-relative layout stays fixed)

Short or wrong-key accounts fail closed (sentinel `0`). Length gates use `UInt64` constants so
extraction sees the same shape as other account-length checks (e.g. Phoenix profile).
-/

namespace Examples.Svm.InstructionsSlice

open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Instructions sysvar / fixture at physical account 1. -/
@[pf_inline] def instructionsAccount : Account.Handle := Account.Handle.at 1

/-- Compile-time total serialized length including trailing current-index `u16`. -/
def serializedBytesNat : Nat := 24
def serializedBytes : UInt64 := 24
def markerMinLen : UInt64 := 16
def markerWordIndex : Nat := 1

@[pf_inline] def grantsInstructions (account : Account.Handle) : Bool :=
  account.key.equals Sysvar.instructionsKey

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

/-- Ordinary managed-state mutate so the module stays on the standard profile. -/
@[pf_entry]
def touch (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let next := s.dummy + 1
    .ok ({ dummy := next }, next)
  else
    .error .overflow

/-- `1` iff account 1 carries the official Instructions sysvar id. -/
@[pf_entry]
def authenticated (_s : State) : UInt64 :=
  if grantsInstructions instructionsAccount then 1 else 0

/-- `1` iff account 1 currently holds the full compile-time serialized window. -/
@[pf_entry]
def fits (_s : State) : UInt64 :=
  if instructionsAccount.dataLen < serializedBytes then 0 else 1

/-- Little-endian `num_instructions` (`u16` at offset 0). Short → `0`. -/
@[pf_entry]
def numInstructions (_s : State) : UInt64 :=
  Sysvar.numInstructionsAt instructionsAccount serializedBytes

/-- Little-endian current index (`u16` at offset 16 / low half of word 2). Short → `0`. -/
@[pf_entry]
def currentIndex (_s : State) : UInt64 :=
  if instructionsAccount.dataLen < serializedBytes then
    0
  else
    instructionsAccount.dataWord 2 &&& (0xffff : UInt64)

/-- Marker word inside the fixed-offset slice. Short → `0`. -/
@[pf_entry]
def markerWord (_s : State) : UInt64 :=
  if instructionsAccount.dataLen < markerMinLen then
    0
  else
    instructionsAccount.dataWord 1

/-- Combined gate: authenticated ∧ fits → `numInstructions`, else fail-closed `0`. -/
@[pf_entry]
def gatedNum (_s : State) : UInt64 :=
  if grantsInstructions instructionsAccount then
    Sysvar.numInstructionsAt instructionsAccount serializedBytes
  else
    0

end Examples.Svm.InstructionsSlice
