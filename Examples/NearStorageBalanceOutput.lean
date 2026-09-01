import ProofForge

namespace Examples.NearStorageBalanceOutput

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

/-- Output-only diagnostics for the compiler-owned bounded `Option<StorageBalance>` JSON policy.
They do not expose NEP-145 methods or choose the contract's registration-cost economics. -/
@[pf_entry] def none (_state : State) : StorageBalanceResult :=
  { registered := 0, total := ⟨0, 0⟩, available := ⟨0, 0⟩ }

@[pf_entry] def someZero (_state : State) : StorageBalanceResult :=
  { registered := 1, total := ⟨0, 0⟩, available := ⟨0, 0⟩ }

@[pf_entry] def someTwo64 (_state : State) : StorageBalanceResult :=
  { registered := 1, total := ⟨0, 1⟩, available := ⟨0, 0⟩ }

@[pf_entry] def someTwo64PlusOne (_state : State) : StorageBalanceResult :=
  { registered := 1, total := ⟨1, 1⟩, available := ⟨0, 1⟩ }

@[pf_entry] def someAsymmetric (_state : State) : StorageBalanceResult :=
  { registered := 1, total := ⟨2, 1⟩, available := ⟨7, 3⟩ }

@[pf_entry] def someMax (_state : State) : StorageBalanceResult :=
  { registered := 1,
    total := ⟨0xffffffffffffffff, 0xffffffffffffffff⟩,
    available := ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ }

/-- Malformed fixture frames prove presence and inactive-field validation at the output boundary. -/
@[pf_entry] def malformedPresence (_state : State) : StorageBalanceResult :=
  { registered := 2, total := ⟨0, 0⟩, available := ⟨0, 0⟩ }

@[pf_entry] def malformedPresenceMax (_state : State) : StorageBalanceResult :=
  { registered := 0xffffffffffffffff, total := ⟨0, 0⟩, available := ⟨0, 0⟩ }

@[pf_entry] def malformedNoneTotal (_state : State) : StorageBalanceResult :=
  { registered := 0, total := ⟨1, 0⟩, available := ⟨0, 0⟩ }

@[pf_entry] def malformedNoneAvailable (_state : State) : StorageBalanceResult :=
  { registered := 0, total := ⟨0, 0⟩, available := ⟨0, 1⟩ }

end Examples.NearStorageBalanceOutput
