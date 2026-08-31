import ProofForge

/-!
Local 2.6.1 vesting escrow: `lockIn` moves 5 onto contract `esc` and
writes `due = ledgerSqn + 2`. `refund` only succeeds when
`due ≤ ledgerSqn` (the next ledger after lockIn still fails).
Zero wasm params. Public still host -22 and tefBAD_AUTH.
Not Sdk.Payments, not a Map, not XRPL EscrowCreate.
-/
namespace Examples.XrplVest

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | paused
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

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

/-- Take 5 back from `esc` only after `due ≤ ledgerSqn`. -/
@[pf_entry]
def refund (s : State) : Except Error (State × UInt64) :=
  if Pausable.isRunning (Context.peekHaltLit "b5f762798a53d543a014caf8b297cff8f2f937e8") then
    if s.bal ≤ u64Max - (5 : UInt64) then
      if Card.storeSelf ≤ u64Max then
        if (5 : UInt64) ≤ Card.peekSelfEsc then
          if Card.peekSelfDue ≤ Context.ledgerSqn then
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
      .error .overflow
  else
    .error .paused

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplVest
