import ProofForge

/-!
Local 2.6.1 dual timelock: caller `lockIn` moves 5 onto contract `esc`
and writes `due = ledgerSqn + 2`. A `cancel` before due takes `esc`
back. After due, A cancel returns 1; only wallet B `claimB`.
Early B claim returns 1; A calling claimB returns 3.
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map, not XRPL EscrowCancel.
-/
namespace Examples.XrplDual

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

@[pf_inline] def minter : AccountId :=
  Context.accountLit "b5f762798a53d543a014caf8b297cff8f2f937e8"

@[pf_inline] def peer : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if s.bal ≤ u64Max - (5 : UInt64) then
      if Card.storeSelf ≤ u64Max then
        if Card.peekSelfSupp ≤ u64Max - (5 : UInt64) then
          if Context.flushSupp (Card.peekSelfSupp + (5 : UInt64)) ≤ u64Max then
            if Card.restoreCaller ≤ u64Max then
              .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))
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
    .error .paused

/-- Move 5 onto contract `esc` and set `due` two ledgers ahead. -/
@[pf_entry]
def lockIn (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if (5 : UInt64) ≤ s.bal then
      if Card.storeSelf ≤ u64Max then
        if Card.peekSelfEsc ≤ u64Max - (5 : UInt64) then
          if Context.flushEsc (Card.peekSelfEsc + (5 : UInt64)) ≤ u64Max then
            if Context.ledgerSqn ≤ u64Max - (2 : UInt64) then
              if Context.flushDue (Context.ledgerSqn + (2 : UInt64)) ≤ u64Max then
                if Card.restoreCaller ≤ u64Max then
                  .ok ({ bal := s.bal - (5 : UInt64) }, (0 : UInt64))
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
      .error .overflow
  else
    .error .paused

/-- A takes 5 back from `esc` only before `due`. After due → overflow. -/
@[pf_entry]
def cancel (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner minter then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if s.bal ≤ u64Max - (5 : UInt64) then
        if Card.storeSelf ≤ u64Max then
          if (5 : UInt64) ≤ Card.peekSelfEsc then
            if Card.selfDueReached then
              .error .overflow
            else
              if Context.flushEsc (Card.peekSelfEsc - (5 : UInt64)) ≤ u64Max then
                if Card.restoreCaller ≤ u64Max then
                  .ok ({ bal := s.bal + (5 : UInt64) }, (0 : UInt64))
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
      .error .paused
  else
    .error .unauthorized

/-- Wallet B takes 5 from contract `esc` after `due`. Early → overflow.
Anyone else → unauthorized. -/
@[pf_entry]
def claimB (_s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner peer then
    if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
      if Card.storeSelf ≤ u64Max then
        if Card.selfDueReached then
          if (5 : UInt64) ≤ Card.peekSelfEsc then
            if Context.flushEsc (Card.peekSelfEsc - (5 : UInt64)) ≤ u64Max then
              if Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max - (5 : UInt64) then
                if Context.storeOwnerLimbs peer.w0 peer.w1 peer.w2 ≤ u64Max then
                  if Context.flushBal (Context.peekOwnerLimbs peer.w0 peer.w1 peer.w2 + (5 : UInt64)) ≤ u64Max then
                    if Card.restoreCaller ≤ u64Max then
                      if Card.persistCaller ≤ u64Max then
                        .ok ({ bal := Card.persistCaller + (0 : UInt64) }, (0 : UInt64))
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
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .paused
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplDual
