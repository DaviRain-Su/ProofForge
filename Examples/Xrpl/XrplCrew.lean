import ProofForge

/-!
Owner + operator across wallets. Shared card is genesis's ContractData
(`accountLit` rewrites mem[0..19]). Second wallet deploys as owner, `setOp`
writes genesis as operator, genesis `bump`s. Not EVM Roles bitmap.
-/
namespace Examples.Xrpl.XrplCrew
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

/-- Genesis rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh. -/
@[pf_inline] def genesis : ProofForge.Wasm.Xrpl.Runtime.AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

/-- Shared card is genesis's. Deployer (caller) is owner; operator starts zero.
Mentioning `genesis.w0` rewrites mem[0..19] before persist. -/
@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2,
    op0 := genesis.w0 * (0 : UInt64), op1 := genesis.w1 * (0 : UInt64),
    op2 := genesis.w2 * (0 : UInt64), value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwnerOr
      (AccountId.ofLimbs s.owner0 s.owner1 s.owner2)
      (AccountId.ofLimbs s.op0 s.op1 s.op2) then
    if genesis.w0 = genesis.w0 then
      if s.value ≤ u64Max - 1 then
        .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
               op0 := s.op0, op1 := s.op1, op2 := s.op2,
               value := s.value + 1 }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .unauthorized
  else
    .error .unauthorized

/-- Owner nominates the compile-time genesis AccountID as operator. -/
@[pf_entry]
def setOp (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    if genesis.w0 = genesis.w0 then
      .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
             op0 := genesis.w0, op1 := genesis.w1, op2 := genesis.w2,
             value := s.value }, (0 : UInt64))
    else
      .error .unauthorized
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Xrpl.XrplCrew