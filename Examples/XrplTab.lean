import ProofForge

/-!
Four compile-time JSON slots `xs_0`…`xs_3`. `setAt` takes two UINT64s via
`function_param` (index, value). Runtime index dispatch is nested `if` on
literals 0/1/2/3. Out of range → overflow. `sum4` is wrapping add of the
four named slots (not a wasm loop). Not `Storage.Vec`.
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

/-- Write one named slot selected by a runtime index. Not a vector store. -/
@[pf_entry]
def setAt (s : State) (index : UInt64) (value : UInt64) : Except Error (State × UInt64) :=
  if index = 0 then
    .ok ({ xs_0 := value, xs_1 := s.xs_1, xs_2 := s.xs_2, xs_3 := s.xs_3 }, (0 : UInt64))
  else if index = 1 then
    .ok ({ xs_0 := s.xs_0, xs_1 := value, xs_2 := s.xs_2, xs_3 := s.xs_3 }, (0 : UInt64))
  else if index = 2 then
    .ok ({ xs_0 := s.xs_0, xs_1 := s.xs_1, xs_2 := value, xs_3 := s.xs_3 }, (0 : UInt64))
  else if index = 3 then
    .ok ({ xs_0 := s.xs_0, xs_1 := s.xs_1, xs_2 := s.xs_2, xs_3 := value }, (0 : UInt64))
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
