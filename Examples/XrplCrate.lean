import ProofForge

/-!
Local 2.6.1 allowance-funded timelock. A `grant` writes `allw=5` on
the caller card. Wallet B `takeAndLock` cuts A's `allw`+`bal` and
moves 5 onto contract `esc` with `due = ledgerSqn + 2`. A may `cancel`
before due. After due only B `cashB` (burns esc+supp, 192 drops to B).
wasm v0 rejects `&&` / `||`; `!cond` extracts. Not Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplCrate

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

/-- Caller writes `allw=5` on this card. -/
@[pf_entry]
def grant (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerAllw (5 : UInt64)) then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max) then
    .error .overflow
  else
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))

/-- Wallet B consumes A's `allw`+`bal` into contract `esc` with due+2.
No grant / short allw → 1. Anyone else → 3. -/
@[pf_entry]
def takeAndLock (_s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner peer then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !((5 : UInt64) ≤ Context.peekAllwLimbs minter.w0 minter.w1 minter.w2) then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekBalLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .overflow
  else if !Gate.ok (Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .overflow
  else if !Gate.ok (Context.flushAllw (Context.peekAllwLimbs minter.w0 minter.w1 minter.w2 - (5 : UInt64))) then
    .error .overflow
  else if !Card.subBalLit "b5f762798a53d543a014caf8b297cff8f2f937e8" (5 : UInt64) then
    .error .overflow
  else if !Card.addSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Card.setSelfDueAhead (2 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

/-- A takes 5 back from `esc` only before `due`. After due → 1. -/
@[pf_entry]
def cancel (s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner minter then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if Card.selfDueReached then
    .error .overflow
  else if !Card.subSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

/-- Wallet B burns 5 from contract `esc`+`supp` after `due` and emits
192 drops to B. Early → 1. Anyone else → 3. -/
@[pf_entry]
def cashB (_s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner peer then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.selfDueReached then
    .error .overflow
  else if !Card.subSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Card.subSelfSupp (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Pay.emitToLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350") then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplCrate
