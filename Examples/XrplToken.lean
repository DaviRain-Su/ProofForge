import ProofForge

/-!
Local 2.6.1 token: treasury plus minter pause and per-card freeze.
Create on 2.6.1 rejects a 14-export Functions array (`temARRAY_TOO_LARGE`),
so this program keeps 11 exports. Cap/operator stay on `XrplFund`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplToken

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

@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_inline] def peer : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Credit 5. Pause-gated. -/
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

/-- Minter claws 5 points from wallet B and cuts contract `supp`.
Works on a frozen card. `flushBal` on B overwrites `$bal`; persist must
peek the caller card, not `s.bal`. -/
@[pf_entry]
def clawB (_s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if (5 : UInt64) ≤ Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 then
            if Context.flushSupp
                (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 - (5 : UInt64)) ≤ u64Max then
              if Context.storeOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max then
                if Context.flushBal (Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 - (5 : UInt64)) ≤ u64Max then
                  if Card.restoreCaller ≤ u64Max then
                    if Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                      .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + (0 : UInt64) }, (0 : UInt64))
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
          .error .overflow
      else
        .error .overflow
    else
      .error .paused
  else
    .error .unauthorized

/-- Caller burns 5 of own points and cuts contract `supp`. Pause- and freeze-gated. -/
@[pf_entry]
def burn (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.callerUnlocked then
      if (5 : UInt64) ≤ s.bal then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 then
            if Context.flushSupp
                (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 - (5 : UInt64)) ≤ u64Max then
              if Card.restoreCaller ≤ u64Max then
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
      .error .frozen
  else
    .error .paused

/-- Burn 5 points and emit 192 drops to the caller. Pause- and freeze-gated. -/
@[pf_entry]
def cashSelf (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.callerUnlocked then
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

end Examples.XrplToken
