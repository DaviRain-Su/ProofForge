import ProofForge

/-!
Local 2.6.1 fund pool: caller cards, contract `supp`, minter pause,
per-user freeze, internal send to wallet B, cash 192 drops to B.
Zero wasm params: 2.6.1 cannot sign Function.ParameterType.
Public AlphaNet: program card -22, emit -196. Not Sdk.Payments, not a Map.
`State.bal` stays the caller's card so persist does not copy `supp`/`halt`/`lock`.
-/
namespace Examples.XrplPool

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  | paused
  | frozen
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Genesis `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`. -/
@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

/-- Wallet B `rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG`. -/
@[pf_inline] def peer : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Credit 5 onto this caller's card and bump contract-owned `supp`.
Pause-gated. Freeze does not block credit. -/
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

/-- Move 5 points from the caller card onto wallet B. Pause- and freeze-gated
on both cards. Peek dest first so a failed send does not debit the caller. -/
@[pf_entry]
def sendToB (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.callerUnlocked then
      if Card.unlocked peer.w0 peer.w1 peer.w2 then
        if (5 : UInt64) ≤ s.bal then
          if Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max - (5 : UInt64) then
            if Card.restoreCaller ≤ u64Max then
              if Context.flushBal (s.bal - (5 : UInt64)) ≤ u64Max then
                .ok ({ bal := Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 + (5 : UInt64) }, (0 : UInt64))
              else
                .error .overflow
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .frozen
    else
      .error .frozen
  else
    .error .paused

/-- Burn 5 points (caller `bal` + contract `supp`) and emit 192 drops to B. -/
@[pf_entry]
def cashToB (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.callerUnlocked then
      if (5 : UInt64) ≤ s.bal then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 then
            if Context.flushSupp
                (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 - (5 : UInt64)) ≤ u64Max then
              if Card.restoreCaller ≤ u64Max then
                if Pay.emitToLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350" ≤ u64Max then
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
      .error .frozen
  else
    .error .paused

/-- Caller writes `lock=1` on *this* card. -/
@[pf_entry]
def freeze (s : State) : Except Error (State × UInt64) :=
  if Card.restoreCaller ≤ u64Max then
    if Context.flushLock (1 : UInt64) ≤ u64Max then
      if s.bal ≤ u64Max then
        .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Caller writes `lock=0` on *this* card. -/
@[pf_entry]
def unfreeze (s : State) : Except Error (State × UInt64) :=
  if Card.restoreCaller ≤ u64Max then
    if Context.flushLock (0 : UInt64) ≤ u64Max then
      if s.bal ≤ u64Max then
        .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Minter writes `halt=1` onto its own card. -/
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

end Examples.XrplPool
