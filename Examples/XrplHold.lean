import ProofForge

/-!
Zero-arg Ownable + Pausable for public AlphaNet. `initialize` records the
caller as owner with `paused = 0`. Owner `pause` writes 1; a later `bump`
returns wasm status 4 and leaves `value`. `unpause` restores running.
No function parameters: AlphaNet public RPC 502s ContractCall Parameters.
-/
namespace Examples.XrplHold

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  paused : UInt64
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  | paused
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2,
    paused := Pausable.running, value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    if Pausable.isRunning s.paused then
      if s.value ≤ u64Max - 1 then
        .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
               paused := s.paused, value := s.value + 1 }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .paused
  else
    .error .unauthorized

@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           paused := Pausable.paused, value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           paused := Pausable.running, value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.XrplHold
