import ProofForge

/-!
Local 2.6.1 allowance take then cashSelf. A `grant` writes `allw=5`.
Wallet B `takeB` cuts A's `allw`+`bal` onto B. B `cashSelf` burns 5
and emits 192 drops. Ungranted take returns 1. Frozen take/cash
returns 5. Anyone else take → 3.
wasm v0 rejects `&&` / `||`; `!cond` extracts. Not Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplRake

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

@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_inline] def peer : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Card.addSelfSupp (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

/-- Lock this caller. `{ bal := s.bal }` would copy the previous
persist Owner's card (A's 10) onto B. -/
@[pf_entry]
def freeze (_s : State) : Except Error (State × UInt64) :=
  if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerLock (1 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def unfreeze (_s : State) : Except Error (State × UInt64) :=
  if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerLock (0 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

/-- Caller writes `allw=5` on this card. -/
@[pf_entry]
def grant (_s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerAllw (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

/-- Wallet B takes 5 from A if `allw≥5`. Cuts `allw`+A `bal`. Credit
lands on B via `{ bal := persistCaller + 5 }` after `restoreCaller`
(same as `XrplTake`). `addBalLit` B then `persistCaller + 0` would
rewrite B to the entry-empty card. No grant → 1. Frozen → 5.
Anyone else → 3. -/
@[pf_entry]
def takeB (s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner peer then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !Card.unlocked minter.w0 minter.w1 minter.w2 then
    .error .frozen
  else if !((5 : UInt64) ≤ Context.peekAllwLimbs minter.w0 minter.w1 minter.w2) then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekBalLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok (Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .overflow
  else if !Gate.ok (Context.flushAllw (Context.peekAllwLimbs minter.w0 minter.w1 minter.w2 - (5 : UInt64))) then
    .error .overflow
  else if !Card.subBalLit "b5f762798a53d543a014caf8b297cff8f2f937e8" (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (5 : UInt64) }, (0 : UInt64))

/-- Caller burns 5, cuts `supp`, emits 192 drops. Frozen → 5. -/
@[pf_entry]
def cashSelf (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !((5 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Context.flushBal (s.bal - (5 : UInt64))) then
    .error .overflow
  else if !Card.subSelfSupp (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok Pay.emitToCaller then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplRake
