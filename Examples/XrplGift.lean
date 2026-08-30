import ProofForge

/-!
Local 2.6.1: `Pay.emitToLit` pays 192 drops to a compile-time AccountID
(wallet B). Public AlphaNet is tefBAD_AUTH -196. Not Sdk.Payments.
Zero wasm params: local 2.6.1 cannot sign Function.ParameterType.
-/
namespace Examples.XrplGift

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

/-- Pay 192 drops to wallet B (`d0bc2a540b15411f44a24dfb58d23ad5d9d9b350`). -/
@[pf_entry]
def ping (s : State) : Except Error (State × UInt64) :=
  if Pay.emitToLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350" ≤ u64Max then
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplGift
