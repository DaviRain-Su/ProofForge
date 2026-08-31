import ProofForge

/-!
Local 2.6.1: same escrow as XrplHoldEsc, written with `Gate.and2` / `Gate.ok`
instead of a pyramid of `if`. wasm v0 still rejects `&&` / `||` / `bitAnd`;
`Gate.and2` is nested `if`. Sequential `flush*` stay nested `if Gate.ok`
because they are effects, not AND.
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
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Gate.and2 (s.bal ≤ Gate.u64Max - (5 : UInt64)) (Gate.ok Card.storeSelf) then
      if Gate.and2
          (Card.peekSelfSupp ≤ Gate.u64Max - (5 : UInt64))
          (Gate.ok (Context.flushSupp (Card.peekSelfSupp + (5 : UInt64)))) then
        if Gate.ok Card.restoreCaller then
          .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Move 5 from the caller card onto contract `esc`. -/
@[pf_entry]
def latch (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Gate.and2 ((5 : UInt64) ≤ s.bal) (Gate.ok Card.storeSelf) then
      if Gate.and2
          (Card.peekSelfEsc ≤ Gate.u64Max - (5 : UInt64))
          (Gate.ok (Context.flushEsc (Card.peekSelfEsc + (5 : UInt64)))) then
        if Gate.ok Card.restoreCaller then
          .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Take 5 back from contract `esc`. -/
@[pf_entry]
def unlatch (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Gate.and2 (s.bal ≤ Gate.u64Max - (5 : UInt64)) (Gate.ok Card.storeSelf) then
      if Gate.and2
          ((5 : UInt64) ≤ Card.peekSelfEsc)
          (Gate.ok (Context.flushEsc (Card.peekSelfEsc - (5 : UInt64)))) then
        if Gate.ok Card.restoreCaller then
          .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplLatch
