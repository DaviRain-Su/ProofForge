import ProofForge

/-!
Local 2.6.1 pause+freeze redemption at a fixed 384-drop rate.
Two `credit`s make bal/supp=10. `cash384` burns 10 and emits 384
drops to the caller. Paused cash returns 4; frozen cash returns 5.
wasm v0 rejects `&&` / `||`; `!cond` extracts. Not Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplRate

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | paused
  | frozen
  deriving Repr, DecidableEq, Inhabited, BEq

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

@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if !Card.flushHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8" Pausable.paused then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max) then
    .error .overflow
  else
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if !Card.flushHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8" Pausable.running then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !(s.bal ≤ Gate.u64Max) then
    .error .overflow
  else
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))

/-- Burn 10 points and emit 384 drops to the caller. Frozen → 5. -/
@[pf_entry]
def cash384 (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !((10 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Context.flushBal (s.bal - (10 : UInt64))) then
    .error .overflow
  else if !Card.subSelfSupp (10 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else if !Gate.ok (Pay.emitToCallerDrops (384 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.persistCaller then
    .error .overflow
  else
    .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplRate
