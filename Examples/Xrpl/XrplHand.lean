import ProofForge

/-!
Two-step Ownable with a compile-time pending AccountID (genesis wallet).
Live AlphaNet: second wallet deploys and `propose`s genesis; genesis `accept`s.
Not a new Op. Destination hex is the genesis AccountID.
-/
namespace Examples.Xrpl.XrplHand
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

/-- Genesis rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh. -/
@[pf_inline] def genesis : ProofForge.Wasm.Xrpl.Runtime.AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

/-- Shared card is genesis's ContractData: mentioning `genesis` rewrites mem[0..19]
before load/persist. Deployer (caller) is recorded as owner on that card. -/
@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2,
    pend0 := genesis.w0, pend1 := genesis.w1, pend2 := genesis.w2, value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    if genesis.w0 = genesis.w0 then
      if s.value ≤ u64Max - 1 then
        .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
               pend0 := s.pend0, pend1 := s.pend1, pend2 := s.pend2,
               value := s.value + 1 }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .unauthorized
  else
    .error .unauthorized

/-- Owner nominates the compile-time genesis AccountID (already the shared-card owner). -/
@[pf_entry]
def propose (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           pend0 := genesis.w0, pend1 := genesis.w1, pend2 := genesis.w2,
           value := s.value }, (0 : UInt64))
  else
    .error .unauthorized

/-- Pending account becomes owner. Genesis wallet can accept after a second-wallet propose. -/
@[pf_entry]
def accept (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.pend0 s.pend1 s.pend2) then
    if genesis.w0 = genesis.w0 then
      .ok ({ owner0 := s.pend0, owner1 := s.pend1, owner2 := s.pend2,
             pend0 := 0, pend1 := 0, pend2 := 0, value := s.value }, (0 : UInt64))
    else
      .error .unauthorized
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Xrpl.XrplHand