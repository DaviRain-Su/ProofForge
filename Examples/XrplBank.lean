import ProofForge

/-!
Local 2.6.1 gated vault: caller `bal` + contract `supp`, minter `halt`,
`cash` burns 5 points and emits 192 drops. Pause blocks credit/cash (status 4).
Public AlphaNet: program card -22, emit -196. Not Sdk.Payments, not a Map.
`State.bal` stays the caller's card so persist does not copy `supp` / `halt`.
-/
namespace Examples.XrplBank

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  | paused
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Genesis `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`. -/
@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Credit 5 onto this caller's card and bump contract-owned `supp`.
Pause-gated. Restore caller before persist. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if s.bal ≤ u64Max - (5 : UInt64) then
      if Card.storeSelf ≤ u64Max then
        if Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 ≤ u64Max - (5 : UInt64) then
          if Context.flushSupp
              (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 + (5 : UInt64)) ≤ u64Max then
            if Card.restoreCaller ≤ u64Max then
              .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Burn 5 points and emit 192 drops to the caller. Pause-gated. -/
@[pf_entry]
def cash (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if (5 : UInt64) ≤ s.bal then
      if Card.storeSelf ≤ u64Max then
        if (5 : UInt64) ≤ Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 then
          if Context.flushSupp
              (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 - (5 : UInt64)) ≤ u64Max then
            if Card.restoreCaller ≤ u64Max then
              if Pay.emitToCaller ≤ u64Max then
                .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))
              else
                .error .overflow
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Minter writes `halt=1` onto its own card. Persist `s.bal`. -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
      if Context.flushHalt Pausable.paused ≤ u64Max then
        if s.bal ≤ u64Max then
          .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .unauthorized

/-- Minter writes `halt=0` onto its own card. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
      if Context.flushHalt Pausable.running ≤ u64Max then
        if s.bal ≤ u64Max then
          .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplBank
