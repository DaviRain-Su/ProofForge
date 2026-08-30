import ProofForge

/-!
Internal points transfer with a per-user freeze (`lock`) on each caller
card. Not XRP, not a Payment, not Sdk.Map, not global `halt`.
`State` stays one `bal` slot so persist does not copy `lock` onto dest
cards. Outgoing and incoming `pay` both fail status 5 while that card
is frozen. `credit` / `freeze` / `unfreeze` stay on the caller card.
-/
namespace Examples.XrplLock

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | frozen
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Add `delta` to *this caller's* card. Freeze does not block credit. -/
@[pf_entry]
def credit (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - delta then
    .ok ({ bal := s.bal + delta }, (0 : UInt64))
  else
    .error .overflow

/-- Caller writes `lock=1` on *this* card. Restore caller before persist. -/
@[pf_entry]
def freeze (s : State) : Except Error (State × UInt64) :=
  if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
    if Context.flushLock (1 : UInt64) ≤ u64Max then
      if s.bal ≤ u64Max then
        .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Caller writes `lock=0` on *this* card. -/
@[pf_entry]
def unfreeze (s : State) : Except Error (State × UInt64) :=
  if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
    if Context.flushLock (0 : UInt64) ≤ u64Max then
      if s.bal ≤ u64Max then
        .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Move `amount` from the caller card onto `(w0,w1,w2)`'s card.
Caller `lock` or dest `lock` (nonzero) is frozen. Peek dest lock/bal
first so a failed `pay` does not debit the caller. Then restore caller
`flushBal` and credit dest. -/
@[pf_entry]
def pay (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64) then
    if Context.peekLockLimbs w0 w1 w2 = (0 : UInt64) then
      if amount ≤ s.bal then
        if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
          if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
            if Context.flushBal (s.bal - amount) ≤ u64Max then
              .ok ({ bal := Context.peekOwnerLimbs w0 w1 w2 + amount }, (0 : UInt64))
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

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplLock
