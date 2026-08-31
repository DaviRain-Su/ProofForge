import ProofForge

/-!
Local 2.6.1 escrow written as else-if guards, not a then-pyramid.
wasm v0 rejects `&&` / `||` / `bitAnd`; `!cond` is `Not`, which extracts.
Sequential `flush*` stay in source order because each `Gate.ok` is an
effect in the next guard. Not `do` / `Except.bind` / Rust `?`.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplLatch

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | paused
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

/-- Move 5 from the caller card onto contract `esc`. -/
@[pf_entry]
def latch (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !((5 : UInt64) ≤ s.bal) then
    .error .overflow
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !(Card.peekSelfEsc ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok (Context.flushEsc (Card.peekSelfEsc + (5 : UInt64))) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))

/-- Take 5 back from contract `esc`. -/
@[pf_entry]
def unlatch (s : State) : Except Error (State × UInt64) :=
  if !Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    .error .paused
  else if !(s.bal ≤ Gate.u64Max - (5 : UInt64)) then
    .error .overflow
  else if !Gate.ok Card.storeSelf then
    .error .overflow
  else if !((5 : UInt64) ≤ Card.peekSelfEsc) then
    .error .overflow
  else if !Gate.ok (Context.flushEsc (Card.peekSelfEsc - (5 : UInt64))) then
    .error .overflow
  else if !Gate.ok Card.restoreCaller then
    .error .overflow
  else
    .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplLatch
