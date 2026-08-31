import ProofForge

/-!
Local 2.6.1 allowance: caller `grant` writes `allw=5` on this card;
wallet B `takeB` moves 5 from A onto B and cuts `allw`. Pause/freeze
gated. 9 exports. Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplTake

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

/-- Caller writes `allw=5` on *this* card. Compile-time spender is wallet B. -/
@[pf_entry]
def grant (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Card.restoreCaller ≤ u64Max then
      if Card.flushCallerAllw (5 : UInt64) ≤ u64Max then
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

/-- Wallet B takes 5 from A's card if `allw≥5`. Cuts `allw`. Freeze-gated
on both cards. Peek dest first so a failed take does not debit A. -/
@[pf_entry]
def takeB (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner peer then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Card.callerUnlocked then
        if Card.unlocked minter.w0 minter.w1 minter.w2 then
          if (5 : UInt64) ≤ Context.peekAllwLimbs minter.w0 minter.w1 minter.w2 then
            if (5 : UInt64) ≤ Context.peekOwnerLimbs minter.w0 minter.w1 minter.w2 then
              if s.bal ≤ u64Max - (5 : UInt64) then
                if Context.storeOwnerLimbs minter.w0 minter.w1 minter.w2 ≤ u64Max then
                  if Context.flushAllw (Context.peekAllwLimbs minter.w0 minter.w1 minter.w2 - (5 : UInt64)) ≤ u64Max then
                    if Context.flushBal (Context.peekOwnerLimbs minter.w0 minter.w1 minter.w2 - (5 : UInt64)) ≤ u64Max then
                      if Card.restoreCaller ≤ u64Max then
                        if Card.persistCaller ≤ u64Max then
                          .ok ({ bal := Card.persistCaller + (5 : UInt64) }, (0 : UInt64))
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
          .error .frozen
      else
        .error .frozen
    else
      .error .paused
  else
    .error .unauthorized

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

end Examples.XrplTake
