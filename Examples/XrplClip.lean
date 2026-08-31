import ProofForge

/-!
Local 2.6.1 freeze-gated dual timelock with claw.
A `sendToB` moves 5 onto wallet B; minter `clawB` takes it back and
cuts contract `supp`. `lockIn` moves 5 onto contract `esc` with
`due = ledgerSqn + 5`. Frozen cancel/cashB return 5. After due only
wallet B `cashB` (burns esc+supp, 192 drops to B).
wasm v0 rejects `&&` / `||`; `!cond` extracts. Not Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplClip

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

/-- Move 5 from the caller card onto wallet B. Frozen → 5. -/
@[pf_entry]
def sendToB (s : State) : Except Error (State × UInt64) :=
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
  else if !Card.addBalLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350" (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

/-- Minter claws 5 from wallet B and cuts contract `supp`.
`flushBal` on B overwrites `$bal`; persist peeks the caller card. -/
@[pf_entry]
def clawB (_s : State) : Except Error (State × UInt64) :=
  if !Access.requireOwner minter then
    .error .unauthorized
  else if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.subSelfSupp (5 : UInt64) then
    .error .overflow
  else if !Card.subBalLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350" (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

/-- Move 5 onto contract `esc` and set `due` five ledgers ahead. Frozen → 5. -/
@[pf_entry]
def lockIn (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !((5 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Card.addSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Card.setSelfDueAhead (5 : UInt64) then
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
  else if Card.selfDueReached then
    .error .overflow
  else if !Card.subSelfEsc (5 : UInt64) then
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

end Examples.XrplClip
