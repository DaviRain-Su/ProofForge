import ProofForge

/-!
Owner-gated mint plus anyone-can-pay points, with a pause flag (`halt`),
total supply (`supp`), mint cap (`cap`, 0 = unlimited), a compile-time
spender allowance (`allw`), and a per-user freeze (`lock`) on each caller
card. Not XRP, not Sdk.Map, not PDA.
`State` stays one `bal` slot so persist does not copy those keys onto dest
cards.
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
  | frozen
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Genesis `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`. -/
@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

/-- Wallet B `rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG`. Compile-time spender. -/
@[pf_inline] def spender : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Only the compile-time minter may add `delta` to *this caller's* card.
Bump `supp` on the minter card, then restore caller before persist.
`cap=0` (missing) is unlimited. -/
@[pf_entry]
def mint (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64) then
        if Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" = (0 : UInt64) then
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
        else if delta ≤ Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" then
          if Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤
              Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" - delta then
            if s.bal ≤ u64Max - delta then
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
          .error .overflow      else
        .error .frozen

    else
      .error .paused
  else
    .error .unauthorized

/-- Minter credits `(w0,w1,w2)`'s card. Peek dest first so overflow is a no-op. -/
@[pf_entry]
def mintTo (_s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.peekLockLimbs w0 w1 w2 = (0 : UInt64) then
        if Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" = (0 : UInt64) then
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
        else if amount ≤ Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" then
          if Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤
              Context.peekCapLit "b5f762798a53d543a014caf8b297cff8f2f937e8" - amount then
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
          .error .overflow      else
        .error .frozen

    else
      .error .paused
  else
    .error .unauthorized

/-- Move `amount` from the caller card onto `(w0,w1,w2)`'s card.
Peek dest first so overflow does not debit the caller. Self-pay only
restores caller `bal` (no debit/credit of the same card). Peek halt on
the minter card, then restore caller before debit so `$bal` is not
copied from the minter. -/
@[pf_entry]
def pay (_s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64) then
      if Context.peekLockLimbs w0 w1 w2 = (0 : UInt64) then
        if amount ≤ Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 then
          if w0 = Context.callerW0 then
            if w1 = Context.callerW1 then
              if w2 = Context.callerW2 then
                if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                  if Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                    .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + (0 : UInt64) }, (0 : UInt64))
                  else
                    .error .overflow
                else
                  .error .overflow
              else if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
                if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                  if Context.flushBal
                      (Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 - amount) ≤ u64Max then
                    .ok ({ bal := Context.peekOwnerLimbs w0 w1 w2 + amount }, (0 : UInt64))
                  else
                    .error .overflow
                else
                  .error .overflow
              else
                .error .overflow
            else if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
              if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                if Context.flushBal
                    (Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 - amount) ≤ u64Max then
                  .ok ({ bal := Context.peekOwnerLimbs w0 w1 w2 + amount }, (0 : UInt64))
                else
                  .error .overflow
              else
                .error .overflow
            else
              .error .overflow
          else if Context.peekOwnerLimbs w0 w1 w2 ≤ u64Max - amount then
            if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
              if Context.flushBal
                  (Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 - amount) ≤ u64Max then
                .ok ({ bal := Context.peekOwnerLimbs w0 w1 w2 + amount }, (0 : UInt64))
              else
                .error .overflow
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow    else
        .error .frozen
    else
      .error .frozen

  else
    .error .paused

/-- Burn `amount` from *this caller's* card. Pause-gated. Underflow is a no-op.
Decrements `supp` on the minter card. Peek halt/supp on the minter card,
then restore caller before persist so `$bal` is not copied from the minter. -/
@[pf_entry]
def burn (_s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64) then
      if amount ≤ Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 then
        if amount ≤ Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" then
          if Context.flushSupp
              (Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" - amount) ≤ u64Max then
            if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
              .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 - amount }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow    else
      .error .frozen

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

/-- Minter writes `cap` onto its own card. `0` = unlimited. A nonzero cap
below current `supp` is a no-op. Pause-gated. Persist `s.bal` so the
extractor keeps a field projection. -/
@[pf_entry]
def setCap (s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if n = (0 : UInt64) then
        if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
          if Context.flushCap n ≤ u64Max then
            if s.bal ≤ u64Max then
              .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else if Context.peekSuppLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ n then
        if Context.storeOwnerLit "b5f762798a53d543a014caf8b297cff8f2f937e8" ≤ u64Max then
          if Context.flushCap n ≤ u64Max then
            if s.bal ≤ u64Max then
              .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
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

/-- Caller writes `allw` on *this* card. Granted to the compile-time spender.
Peek halt on the minter card, then restore caller before persist so `$bal`
is not copied from the minter. -/
@[pf_entry]
def approve (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
      if Context.flushAllw amount ≤ u64Max then
        if Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
          .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + (0 : UInt64) }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .paused

/-- Compile-time spender pulls `amount` from `(w0,w1,w2)`'s card onto this
caller card. Cuts that card's `allw`. Self-source only cuts `allw` (no
debit/credit of the same card). Underflow / missing allowance is a no-op.
Same `storeOwnerLimbs` rewrite as `pay`. Not a Map. -/
@[pf_entry]
def takeFrom (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner spender then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Context.peekLockLimbs w0 w1 w2 = (0 : UInt64) then
        if Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64) then
          if amount ≤ Context.peekAllwLimbs w0 w1 w2 then
            if w0 = Context.callerW0 then
              if w1 = Context.callerW1 then
                if w2 = Context.callerW2 then
                  if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                    if Context.flushAllw (Context.peekAllwLimbs w0 w1 w2 - amount) ≤ u64Max then
                      if Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                        .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + (0 : UInt64) }, (0 : UInt64))
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else if amount ≤ Context.peekOwnerLimbs w0 w1 w2 then
                  if s.bal ≤ u64Max - amount then
                    if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
                      if Context.flushAllw (Context.peekAllwLimbs w0 w1 w2 - amount) ≤ u64Max then
                        if Context.flushBal (Context.peekOwnerLimbs w0 w1 w2 - amount) ≤ u64Max then
                          if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                            .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + amount }, (0 : UInt64))
                          else
                            .error .overflow
                        else
                          .error .overflow
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else
                  .error .overflow
              else if amount ≤ Context.peekOwnerLimbs w0 w1 w2 then
                if s.bal ≤ u64Max - amount then
                  if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
                    if Context.flushAllw (Context.peekAllwLimbs w0 w1 w2 - amount) ≤ u64Max then
                      if Context.flushBal (Context.peekOwnerLimbs w0 w1 w2 - amount) ≤ u64Max then
                        if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                          .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + amount }, (0 : UInt64))
                        else
                          .error .overflow
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else
                  .error .overflow
              else
                .error .overflow
            else if amount ≤ Context.peekOwnerLimbs w0 w1 w2 then
              if s.bal ≤ u64Max - amount then
                if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
                  if Context.flushAllw (Context.peekAllwLimbs w0 w1 w2 - amount) ≤ u64Max then
                    if Context.flushBal (Context.peekOwnerLimbs w0 w1 w2 - amount) ≤ u64Max then
                      if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
                        .ok ({ bal := Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 + amount }, (0 : UInt64))
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else
                  .error .overflow
              else
                .error .overflow
            else
              .error .overflow
          else
            .error .overflow      else
          .error .frozen
      else
        .error .frozen

    else
      .error .paused
  else
    .error .unauthorized


/-- Caller writes `lock=1` on *this* card. Restore caller before persist.
Not global `halt`. -/
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

/-- Minter writes `lock=1` onto `(w0,w1,w2)`'s card. Restore caller before
persist so `$bal` is not copied onto the dest card. Not a PDA. -/
@[pf_entry]
def freezeOf (s : State) (w0 w1 w2 : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
      if Context.flushLock (1 : UInt64) ≤ u64Max then
        if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
          if s.bal ≤ u64Max then
            .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .unauthorized

/-- Minter writes `lock=0` onto `(w0,w1,w2)`'s card. Restore caller before persist. -/
@[pf_entry]
def unfreezeOf (s : State) (w0 w1 w2 : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
      if Context.flushLock (0 : UInt64) ≤ u64Max then
        if Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2 ≤ u64Max then
          if s.bal ≤ u64Max then
            .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
          else
            .error .overflow
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
