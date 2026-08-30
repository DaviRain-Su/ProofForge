import ProofForge

/-!
Local 2.6.1 share: minter `mintToB`, caller `cashToB` (192 drops to B),
`clawB`, pause/freeze. 11 exports (`temARRAY_TOO_LARGE` at 14).
Uses `Card.persistCaller` after dest `flushBal`. Zero wasm params.
Public still host -22 and tefBAD_AUTH. Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplShare

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

/-- Credit 5 onto the caller card. Pause-gated. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if s.bal ≤ u64Max - (5 : UInt64) then
      if Card.storeSelf ≤ u64Max then
        if Card.peekSelfSupp ≤ u64Max - (5 : UInt64) then
          if Context.flushSupp (Card.peekSelfSupp + (5 : UInt64)) ≤ u64Max then
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

/-- Minter credits 5 onto wallet B and bumps contract `supp`. -/
@[pf_entry]
def mintToB (_s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max - (5 : UInt64) then
        if Card.storeSelf ≤ u64Max then
          if Card.peekSelfSupp ≤ u64Max - (5 : UInt64) then
            if Context.flushSupp (Card.peekSelfSupp + (5 : UInt64)) ≤ u64Max then
              if Context.storeOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max then
                if Context.flushBal (Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 + (5 : UInt64)) ≤ u64Max then
                  if Card.restoreCaller ≤ u64Max then
                    if Card.persistCaller ≤ u64Max then
                      .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))
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

/-- Move 5 points from the caller card onto wallet B. -/
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

/-- Minter claws 5 from B and cuts `supp`. Frozen cards still claw. -/
@[pf_entry]
def clawB (_s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if (5 : UInt64) ≤ Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Card.peekSelfSupp then
            if Context.flushSupp (Card.peekSelfSupp - (5 : UInt64)) ≤ u64Max then
              if Context.storeOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max then
                if Context.flushBal (Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 - (5 : UInt64)) ≤ u64Max then
                  if Card.restoreCaller ≤ u64Max then
                    if Card.persistCaller ≤ u64Max then
                      .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))
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

/-- Burn 5 caller points and emit 192 drops to wallet B. -/
@[pf_entry]
def cashToB (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.callerUnlocked then
      if (5 : UInt64) ≤ s.bal then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Card.peekSelfSupp then
            if Context.flushSupp (Card.peekSelfSupp - (5 : UInt64)) ≤ u64Max then
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

end Examples.XrplShare
