import ProofForge

/-!
Local 2.6.1 freeze-gated dual timelock as else-if guards: A `lockIn`
moves 5 onto contract `esc` with `due = ledgerSqn + 5` (freeze/unfreeze
consume ledgers). Frozen A `cancel` returns 5. After due only wallet B
`cashB` (burns esc+supp, 192 drops to B). Frozen B cash also returns 5.
wasm v0 rejects `&&` / `||`; `!cond` extracts. Not Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not EscrowCancel.
-/
namespace Examples.XrplGlaze

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
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !(Card.peekSelfSupp ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok (Context.flushSupp (Card.peekSelfSupp + (5 : UInt64))) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

@[pf_entry]
def freeze (s : State) : Except Error (State × UInt64) :=
  if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerLock (1 : UInt64)) then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max) then
    .error .overflow
  else
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def unfreeze (s : State) : Except Error (State × UInt64) :=
  if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Card.flushCallerLock (0 : UInt64)) then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max) then
    .error .overflow
  else
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))

/-- Move 5 onto contract `esc` and set `due` five ledgers ahead. Frozen → 5. -/
@[pf_entry]
def lockIn (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !((5 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !(Card.peekSelfEsc ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok (Context.flushEsc (Card.peekSelfEsc + (5 : UInt64))) then
    .error .overflow
  else if !(Context.ledgerSqn ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok (Context.flushDue (Context.ledgerSqn + (5 : UInt64))) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))

/-- A takes 5 back from `esc` only before `due`. Frozen → 5. After due → 1. -/
@[pf_entry]
def cancel (s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner minter then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekSelfEsc) then
    .error .overflow
  else if Card.selfDueReached then
    .error .overflow
  else if !Gate.ok (Context.flushEsc (Card.peekSelfEsc - (5 : UInt64))) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

/-- Wallet B burns 5 from contract `esc`+`supp` after `due` and emits
192 drops to B. Frozen → 5. Early → 1. Anyone else → 3. -/
@[pf_entry]
def cashB (_s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner peer then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !Card.selfDueReached then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekSelfEsc) then
    .error .overflow
  else if !Gate.ok (Context.flushEsc (Card.peekSelfEsc - (5 : UInt64))) then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekSelfSupp) then
    .error .overflow
  else if !Gate.ok (Context.flushSupp (Card.peekSelfSupp - (5 : UInt64))) then
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

end Examples.XrplGlaze
