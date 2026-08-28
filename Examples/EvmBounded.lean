import ProofForge

namespace Examples.EvmBounded

open ProofForge.Core.Value

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ dummy := 1 }, 1) else .error .rejected

/-- A standard-ABI `uint64[]` whose source representation remains a fixed five-word frame:
runtime length followed by four compile-time element slots. -/
@[pf_entry]
def boundedValues (_s : State) (items : BoundedVec UInt64 4) : UInt64 :=
  items.length.toUInt64 + items.values[0] + items.values[3]

/-- Static and bounded-dynamic parameters can share one canonical ABI head. Each dynamic offset is
the exact end of the preceding head/tail; inactive source slots stay zero. -/
@[pf_entry]
def combine (_s : State) (base : UInt32) (left : BoundedVec UInt64 2) (enabled : Bool)
    (right : BoundedVec UInt16 3) : UInt64 :=
  base.toUInt64 + left.length.toUInt64 + left.values[1] +
    (if enabled then (1 : UInt64) else 0) + right.length.toUInt64 +
    right.values[2].toUInt64

end Examples.EvmBounded
