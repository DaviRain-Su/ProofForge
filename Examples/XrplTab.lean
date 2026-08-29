import ProofForge

/-!
Four compile-time JSON slots `xs_0`…`xs_3`. Zero-arg for public AlphaNet.
`sum4` is wrapping add of the four named slots (not a wasm loop). Runtime
`Vector` index still rejected; literal `forAccum` unrolls in Wasm.IR when
the extractor emits it.
-/
namespace Examples.XrplTab

structure State where
  xs_0 : UInt64
  xs_1 : UInt64
  xs_2 : UInt64
  xs_3 : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { xs_0 := 0, xs_1 := 0, xs_2 := 0, xs_3 := 0 }

@[pf_entry]
def fill0 (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ xs_0 := 1, xs_1 := s.xs_1, xs_2 := s.xs_2, xs_3 := s.xs_3 }, (0 : UInt64))
  else
    .error .overflow

/-- Wrapping sum of the four named slots. -/
@[pf_entry]
def sum4 (s : State) : UInt64 :=
  s.xs_0 + s.xs_1 + s.xs_2 + s.xs_3

@[pf_entry]
def get0 (s : State) : UInt64 :=
  s.xs_0

end Examples.XrplTab
