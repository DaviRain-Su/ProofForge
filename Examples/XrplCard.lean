import ProofForge

/-!
Same caller-card pay as `XrplLock`, written through `Sdk.Card` names.
Not XRP, not Sdk.Map, not a PDA. Digest must stay the Lock shape except
for the extra SDK unfold; live AlphaNet checks freeze + pay.
-/
namespace Examples.XrplCard

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

@[pf_entry]
def credit (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - delta then
    .ok ({ bal := s.bal + delta }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def freeze (s : State) : Except Error (State × UInt64) :=
  if Card.restoreCaller ≤ u64Max then
    if Context.flushLock (1 : UInt64) ≤ u64Max then
      if s.bal ≤ u64Max then
        .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

@[pf_entry]
def unfreeze (s : State) : Except Error (State × UInt64) :=
  if Card.restoreCaller ≤ u64Max then
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
`Card.unlocked` rewrites persist Owner; restore caller before debit. -/
@[pf_entry]
def pay (s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Card.callerUnlocked then
    if Card.unlocked w0 w1 w2 then
      if amount ≤ s.bal then
        if Card.peekBal w0 w1 w2 ≤ u64Max - amount then
          if Card.restoreCaller ≤ u64Max then
            if Context.flushBal (s.bal - amount) ≤ u64Max then
              .ok ({ bal := Card.peekBal w0 w1 w2 + amount }, (0 : UInt64))
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

end Examples.XrplCard
