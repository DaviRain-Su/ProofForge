import ProofForge

/-!
Local 2.6.1: `Pay.emitToCallerDrops 384` → STAmount `0x40… | 384`.
Public AlphaNet is tefBAD_AUTH -196. Not Sdk.Payments.
Zero wasm params: local 2.6.1 cannot sign Function.ParameterType.
-/
namespace Examples.XrplTip

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

/-- Pay 384 drops from the funded contract pseudo-account to the caller. -/
@[pf_entry]
def ping (s : State) : Except Error (State × UInt64) :=
  if Pay.emitToCallerDrops (384 : UInt64) ≤ u64Max then
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplTip
