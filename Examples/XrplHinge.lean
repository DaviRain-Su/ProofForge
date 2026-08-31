import ProofForge

/-!
Local 2.6.1 freeze-gated escrow via SDK Card.addSelfEsc / subSelfEsc /
addSelfSupp. Frozen latch/unlatch return 5. Else-if, not `&&`.
Not Rust `?`. Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplHinge

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

/-- Move 5 onto contract `esc`. Frozen caller → 5. -/
@[pf_entry]
def latch (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !((5 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Card.addSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))

/-- Take 5 back from contract `esc`. Frozen caller → 5. -/
@[pf_entry]
def unlatch (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !Card.callerUnlocked then
    .error .frozen
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Card.subSelfEsc (5 : UInt64) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplHinge
