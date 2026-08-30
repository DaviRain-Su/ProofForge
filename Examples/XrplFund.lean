import ProofForge

/-!
Local 2.6.1 fund: XrplPool plus mint cap (`cap` on the minter card) and an
operator flag (`allw=1` on the minter card). Wallet B may pause/unpause
after `grantOp`. `setCap10` writes cap=10; a later `credit` past that
returns overflow. Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplFund

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

/-- Credit 5. Pause-gated. `cap=0` unlimited; else `supp+5` must fit. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" = (0 : UInt64) then
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
    else if (5 : UInt64) ≤ Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" then
      if Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 ≤
          Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" - (5 : UInt64) then
        if s.bal ≤ u64Max - (5 : UInt64) then
          if Card.storeSelf ≤ u64Max then
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
      .error .overflow
  else
    .error .paused

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

/-- Minter writes `cap=10` on its card. Pause-gated. -/
@[pf_entry]
def setCap10 (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
        if Context.flushCap (10 : UInt64) ≤ u64Max then
          if s.bal ≤ u64Max then
            .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
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

/-- Minter writes `allw=1` so wallet B may pause/unpause. -/
@[pf_entry]
def grantOp (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
      if Context.flushAllw (1 : UInt64) ≤ u64Max then
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
  else if Access.requireOwner peer then
    if Context.peekAllwLit "b5f762798a53d543a014caf8b297cff8f2f937e8" = (1 : UInt64) then
      if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
        if Context.flushHalt Pausable.paused ≤ u64Max then
          if Card.restoreCaller ≤ u64Max then
            if s.bal ≤ u64Max then
              .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .unauthorized
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
  else if Access.requireOwner peer then
    if Context.peekAllwLit "b5f762798a53d543a014caf8b297cff8f2f937e8" = (1 : UInt64) then
      if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
        if Context.flushHalt Pausable.running ≤ u64Max then
          if Card.restoreCaller ≤ u64Max then
            if s.bal ≤ u64Max then
              .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .unauthorized
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplFund
