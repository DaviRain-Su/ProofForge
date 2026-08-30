import ProofForge

/-!
Owner-gated mint plus anyone-can-pay points. Not XRP, not Sdk.Map.
Minter is compile-time genesis AccountID (`accountLit`). `State` stays
one `bal` slot so persist does not copy owner limbs onto dest cards.
-/
namespace Examples.XrplMint

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Genesis `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`. -/
@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Only the compile-time minter may add `delta` to *this caller's* card. -/
@[pf_entry]
def mint (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if s.bal ≤ u64Max - delta then
      .ok ({ bal := s.bal + delta }, (0 : UInt64))
    else
      .error .overflow
  else
    .error .unauthorized

/-- Move `amount` from the caller card onto `(w0,w1,w2)`'s card.
Peek dest first so overflow does not debit the caller. Anyone may pay. -/
@[pf_entry]
def pay (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
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

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplMint
