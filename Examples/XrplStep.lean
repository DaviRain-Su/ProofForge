import ProofForge

/-!
Two-step Ownable, zero-arg for public AlphaNet. `propose` copies caller into
pending; `accept` requires caller = pending then writes owner. Not a new Op.
-/
namespace Examples.XrplStep

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  pend0 : UInt64
  pend1 : UInt64
  pend2 : UInt64
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
    pend0 := 0, pend1 := 0, pend2 := 0, value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    if s.value ≤ u64Max - 1 then
      .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
             pend0 := s.pend0, pend1 := s.pend1, pend2 := s.pend2,
             value := s.value + 1 }, (0 : UInt64))
    else
      .error .overflow
  else
    .error .unauthorized

/-- Owner nominates the current caller as pending. Live net has one wallet, so
this is a self-nominate; a second wallet is needed to prove `accept`. -/
@[pf_entry]
def propose (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           pend0 := Context.callerW0, pend1 := Context.callerW1, pend2 := Context.callerW2,
           value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

/-- Pending account becomes owner. -/
@[pf_entry]
def accept (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.pend0 s.pend1 s.pend2) then
    .ok ({ owner0 := s.pend0, owner1 := s.pend1, owner2 := s.pend2,
           pend0 := 0, pend1 := 0, pend2 := 0, value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.XrplStep
