import ProofForge

/-!
Internal points transfer across two caller cards. Not XRP, not a Payment,
not Sdk.Map. `flushBal` writes the caller's reduced `bal`; `peekOwnerLimbs`
rewrites persist Owner and loads the destination card (missing → 0); the
final store credits that card.
-/
namespace Examples.XrplPay

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Add `delta` to *this caller's* card. -/
@[pf_entry]
def credit (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - delta then
    .ok ({ bal := s.bal + delta }, (0 : UInt64))
  else
    .error .overflow

/-- Move `amount` from the caller card onto `(w0,w1,w2)`'s card. -/
@[pf_entry]
def pay (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if amount ≤ s.bal then
    if Context.flushBal (s.bal - amount) ≤ u64Max then
      if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
        .ok ({ bal := Context.peekOwnerLimbs w0 w1 w2 + amount }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplPay
