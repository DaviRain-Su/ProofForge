import ProofForge

/-!
Local 2.6.1: credit 5 onto caller `bal` and contract `supp`, then `cash`
burns 5 points and emits 192 drops to the caller.
Public AlphaNet: program card -22, emit -196. Not Sdk.Payments, not a Map.
`State.bal` stays the caller's card so persist does not copy `supp`.
-/
namespace Examples.XrplCash

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

/-- Credit 5 onto this caller's card and bump contract-owned `supp`. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - (5 : UInt64) then
    if Card.storeSelf ≤ u64Max then
      if Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 ≤ u64Max - (5 : UInt64) then
        if Context.flushSupp
            (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 + (5 : UInt64)) ≤ u64Max then
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

/-- Burn 5 points (caller `bal` + contract `supp`) and emit 192 drops. -/
@[pf_entry]
def cash (s : State) : Except Error (State × UInt64) :=
  if (5 : UInt64) ≤ s.bal then
    if Card.storeSelf ≤ u64Max then
      if (5 : UInt64) ≤ Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 then
        if Context.flushSupp
            (Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2 - (5 : UInt64)) ≤ u64Max then
          if Card.restoreCaller ≤ u64Max then
            if Pay.emitToCaller ≤ u64Max then
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

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplCash
