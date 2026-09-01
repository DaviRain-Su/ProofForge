import ProofForge

/-!
Zero-arg Ownable for public AlphaNet. `initialize` records the caller as
owner; `renounce` zeros the three owner limbs; a later `bump` from the same
wallet must return unauthorized (wasm status 3). No function parameters:
AlphaNet public RPC 502s ContractCall Parameters.
-/
namespace Examples.XrplGate

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- No arguments. Writes the current `ContractCall` account as owner. -/
@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2, value := 0 }

/-- Owner-only increment. Same gate as `XrplOwn`, but callable without Parameters. -/
@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    if s.value ≤ u64Max - 1 then
      .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
             value := s.value + 1 }, (0 : UInt64))
    else
      .error .overflow
  else
    .error .unauthorized

/-- Owner-only: zero the three owner limbs. Later bumps from anyone fail. -/
@[pf_entry]
def renounce (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := 0, owner1 := 0, owner2 := 0, value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.XrplGate
