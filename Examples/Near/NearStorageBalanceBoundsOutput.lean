import ProofForge

namespace Examples.Near.NearStorageBalanceBoundsOutput
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State := { marker }

@[pf_entry]
def get (state : State) : UInt64 := state.marker

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ marker := 1 }, 1) else .error .overflow

/-- Output-only diagnostics for the compiler-owned bounded `StorageBalanceBounds` JSON policy.
They expose no NEP-145 method and choose no contract registration economics. -/
@[pf_entry] def noMaxZero (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 0, max := ⟨0, 0⟩ }

@[pf_entry] def noMaxTwo64 (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 1⟩, hasMax := 0, max := ⟨0, 0⟩ }

@[pf_entry] def someZero (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 1, max := ⟨0, 0⟩ }

@[pf_entry] def someTwo64PlusOne (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨1, 1⟩, hasMax := 1, max := ⟨0, 1⟩ }

@[pf_entry] def someAsymmetric (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨2, 1⟩, hasMax := 1, max := ⟨7, 3⟩ }

@[pf_entry] def someMax (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0xffffffffffffffff, 0xffffffffffffffff⟩,
    hasMax := 1,
    max := ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ }

/-- Malformed frames prove discriminant and inactive-maximum validation at the output boundary. -/
@[pf_entry] def malformedPresence (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 2, max := ⟨0, 0⟩ }

@[pf_entry] def malformedPresenceMax (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 0xffffffffffffffff, max := ⟨0, 0⟩ }

@[pf_entry] def malformedNoneMaxLow (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 0, max := ⟨1, 0⟩ }

@[pf_entry] def malformedNoneMaxHigh (_state : State) : StorageBalanceBoundsResult :=
  { min := ⟨0, 0⟩, hasMax := 0, max := ⟨0, 1⟩ }

end Examples.Near.NearStorageBalanceBoundsOutput