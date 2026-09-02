import ProofForge

namespace Examples.SvmExceptErgonomics

open ProofForge.Core.Except

private def u64Max : UInt64 := ~~~(0 : UInt64)

structure State where
  total : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init (initial : UInt64) : State := ⟨initial⟩

@[pf_entry] def totalOf (state : State) : UInt64 := state.total

private def checkedAdd (a b : UInt64) : Except Error UInt64 :=
  if a ≤ u64Max - b then ok (a + b) else err .overflow

attribute [pf_inline] checkedAdd

/-- SVM consumer of `Core.Except.andThen` for a fallible scalar accumulation chain. -/
@[pf_entry]
def addViaAndThen (state : State) (delta : UInt64) : Except Error (State × UInt64) :=
  andThen (checkedAdd state.total delta) fun sum =>
    ok (⟨sum⟩, sum)

end Examples.SvmExceptErgonomics
