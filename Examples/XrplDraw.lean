import ProofForge

/-!
Local 2.6.1: `Pay.emitToCallerDrops s.bal` — the STAmount mantissa comes from
State (`credit` stores 192; `draw` emits it), not a compile-time literal like
XrplTip's 384. Else-if guards only: wasm v0 has no `&&`/bitAnd. Zero wasm
params: local 2.6.1 cannot sign Function.ParameterType.
Public AlphaNet is tefBAD_AUTH -196. Not Sdk.Payments.
-/
namespace Examples.XrplDraw

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

/-- Credit a fixed 192-drop draw balance onto this caller's state. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - (192 : UInt64) then
    .ok ({ bal := s.bal + (192 : UInt64) }, (0 : UInt64))
  else
    .error .overflow

/-- Emit exactly the stored `s.bal` drops, then zero it. -/
@[pf_entry]
def draw (s : State) : Except Error (State × UInt64) :=
  if s.bal = 0 then
    .error .overflow
  else if Pay.emitToCallerDrops s.bal ≤ u64Max then
    .ok ({ bal := 0 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplDraw