import ProofForge

/-!
Owner-gated mint plus anyone-can-pay points, with a pause flag (`halt`)
and total supply (`supp`) on the minter card. Not XRP, not Sdk.Map.
`State` stays one `bal` slot so persist does not copy pause/supply onto
dest cards.
-/
namespace Examples.XrplMint

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  | paused
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Genesis `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`. -/
@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Only the compile-time minter may add `delta` to *this caller's* card.
Bump `supp` on the minter card, then restore caller before persist. -/
@[pf_entry]
def mint (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if s.bal ≤ u64Max - delta then
        if Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max - delta then
          if Context.flushSupp
              (Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" + delta) ≤ u64Max then
            if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
              .ok ({ bal := s.bal + delta }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .paused
  else
    .error .unauthorized

/-- Minter credits `(w0,w1,w2)`'s card. Peek dest first so overflow is a no-op. -/
@[pf_entry]
def mintTo (_s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max - amount then
        if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
          if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
            if Context.flushSupp
                (Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" + amount) ≤ u64Max then
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
      .error .paused
  else
    .error .unauthorized

/-- Move `amount` from the caller card onto `(w0,w1,w2)`'s card.
Peek dest first so overflow does not debit the caller. Anyone may pay
while running. -/
@[pf_entry]
def pay (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
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
    .error .paused

/-- Burn `amount` from *this caller's* card. Pause-gated. Underflow is a no-op.
Decrements `supp` on the minter card. -/
@[pf_entry]
def burn (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if amount ≤ s.bal then
      if amount ≤ Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" then
        if Context.flushSupp
            (Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" - amount) ≤ u64Max then
          if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
            .ok ({ bal := s.bal - amount }, (0 : UInt64))
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Minter writes `halt=1` onto its own card. Persist `s.bal` so the
extractor keeps a field projection (not a bare State arg). -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
      if Context.flushHalt Pausable.paused ≤ u64Max then
        if s.bal ≤ u64Max then
          .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .unauthorized

/-- Minter writes `halt=0` onto its own card. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
      if Context.flushHalt Pausable.running ≤ u64Max then
        if s.bal ≤ u64Max then
          .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplMint
