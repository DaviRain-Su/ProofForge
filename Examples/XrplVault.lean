import ProofForge

/-!
Shared `supp` on the contract AccountID card via `Card.storeSelf`.
Local transia/alphanet 2.6.1: funded Create then pokeSelf is green.
Public AlphaNet 3.3.0: host -22. Not Sdk.Map, not a Payment.
`State.bal` stays the caller's card so persist does not copy `supp`.
-/
namespace Examples.XrplVault

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

/-- Credit 5 onto this caller's card and bump contract-owned `supp`.
Zero wasm params: local 2.6.1 cannot sign Function.ParameterType.
Restore caller before persist so `$bal` is not copied onto the vault. -/
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

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplVault
