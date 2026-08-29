import ProofForge

/-!
Compile-time named JSON slots `xs_0` / `xs_1` / `xs_2`. Not a Lean `Vector`,
not `set_data_array_element_field` (this Bedrock image traps that host).
Runtime index dispatch is nested `if` on literals 0/1/2. Out of range → overflow.
-/
namespace Examples.XrplVec

structure State where
  xs_0 : UInt64
  xs_1 : UInt64
  xs_2 : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { xs_0 := 0, xs_1 := 0, xs_2 := 0 }

/-- Write one named slot selected by a runtime index. Not a vector store. -/
@[pf_entry]
def setAt (s : State) (index : UInt64) (value : UInt64) : Except Error (State × UInt64) :=
  if index = 0 then
    .ok ({ xs_0 := value, xs_1 := s.xs_1, xs_2 := s.xs_2 }, (0 : UInt64))
  else if index = 1 then
    .ok ({ xs_0 := s.xs_0, xs_1 := value, xs_2 := s.xs_2 }, (0 : UInt64))
  else if index = 2 then
    .ok ({ xs_0 := s.xs_0, xs_1 := s.xs_1, xs_2 := value }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get0 (s : State) : UInt64 :=
  s.xs_0

@[pf_entry]
def get1 (s : State) : UInt64 :=
  s.xs_1

@[pf_entry]
def get2 (s : State) : UInt64 :=
  s.xs_2

end Examples.XrplVec
