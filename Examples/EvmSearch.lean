import ProofForge

namespace Examples.EvmSearch

open ProofForge.Core.Value

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { marker := 0 }

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) == 0 then .ok ({ marker := 1 }, 1) else .error .rejected

/-- A consumer-selected bounded `bytes` policy. Core owns the allocation-free substring scan;
standard ABI owns the two adjacent canonical dynamic tails. -/
@[pf_entry]
def bytesContains (_state : State) (haystack needle : BoundedBytes 3) : Bool :=
  haystack.contains needle

/-- UTF-8 validation remains an ABI boundary invariant before the same bounded byte scan runs. -/
@[pf_entry]
def stringsContains (_state : State) (text needle : BoundedString 3) : Bool :=
  text.contains needle

end Examples.EvmSearch
