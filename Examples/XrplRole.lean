import ProofForge

/-!
Owner plus a second operator limb-triple. `setOp` is owner-only; `bump` allows
either. Zero-arg. Not EVM Roles bitmap.
-/
namespace Examples.XrplRole

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  op0 : UInt64
  op1 : UInt64
  op2 : UInt64
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2,
    op0 := 0, op1 := 0, op2 := 0, value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwnerOr
      (AccountId.ofLimbs s.owner0 s.owner1 s.owner2)
      (AccountId.ofLimbs s.op0 s.op1 s.op2) then
    if s.value ≤ u64Max - 1 then
      .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
             op0 := s.op0, op1 := s.op1, op2 := s.op2,
             value := s.value + 1 }, (0 : UInt64))
    else
      .error .overflow
  else
    .error .unauthorized

/-- Owner writes the current caller as operator. Same-wallet live net is a self-op. -/
@[pf_entry]
def setOp (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           op0 := Context.callerW0, op1 := Context.callerW1, op2 := Context.callerW2,
           value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.XrplRole
