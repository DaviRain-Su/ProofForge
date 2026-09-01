import ProofForge

/-!
SVM consumer of shared bounded UInt64 math. Batch sizing owns its zero-capacity error and state
transition while bounded and saturating operations remain target-neutral pure policy.
-/

namespace Examples.BatchSizer

open ProofForge.Core

structure State where
  lastBatchCount : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | zeroCapacity
  | ratioOverflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (initial : UInt64) : State :=
  { lastBatchCount := initial }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.lastBatchCount

@[pf_entry]
def smaller (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.min left right

@[pf_entry]
def larger (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.max left right

@[pf_entry]
def midpoint (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.average left right

@[pf_entry]
def plan (state : State) (items capacity : UInt64) : Except Error (State × UInt64) := do
  let batches ← Math.UInt64.ceilDiv items capacity .zeroCapacity
  .ok ({ state with lastBatchCount := batches }, batches)

/-- Capacity accumulation clamps rather than turning an oversized external batch into a failure. -/
@[pf_entry]
def reserve (state : State) (additional : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingAdd state.lastBatchCount additional
  .ok ({ state with lastBatchCount := next }, next)

/-- Capacity consumption floors at zero, matching unsigned quota semantics. -/
@[pf_entry]
def consume (state : State) (amount : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingSub state.lastBatchCount amount
  .ok ({ state with lastBatchCount := next }, next)

/-- Scaling an externally supplied capacity clamps to the representable account-state ceiling. -/
@[pf_entry]
def amplify (state : State) (factor : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingMul state.lastBatchCount factor
  .ok ({ state with lastBatchCount := next }, next)

/-- Zero-based binary magnitude for bounded batching and capacity bucketing. -/
@[pf_entry]
def binaryOrder (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log2 value

/-- Zero-based decimal magnitude for human-scale batch limits. -/
@[pf_entry]
def decimalOrder (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log10 value

/-- Zero-based highest occupied byte for fixed account encodings. -/
@[pf_entry]
def byteOrder (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log256 value

/-- Floor square root for two-dimensional capacity partitioning. -/
@[pf_entry]
def capacityRoot (_state : State) (capacity : UInt64) : UInt64 :=
  Math.UInt64.sqrt capacity

/-- First binary order whose power of two covers the capacity. -/
@[pf_entry]
def binaryOrderUp (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log2Ceil value

/-- First decimal order whose power of ten covers the capacity. -/
@[pf_entry]
def decimalOrderUp (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log10Ceil value

/-- First base-256 order whose power covers the encoded value. -/
@[pf_entry]
def byteOrderUp (_state : State) (value : UInt64) : UInt64 :=
  Math.UInt64.log256Ceil value

/-- Smallest square grid dimension that covers the capacity. -/
@[pf_entry]
def capacityRootUp (_state : State) (capacity : UInt64) : UInt64 :=
  Math.UInt64.sqrtCeil capacity

/-- Apply a full-precision fractional capacity weight without overflowing the intermediate
product. A zero total weight and an unrepresentable result remain distinct application errors. -/
@[pf_entry]
def prorate (state : State) (items weight totalWeight : UInt64) :
    Except Error (State × UInt64) := do
  let batches ← Math.UInt64.mulDiv items weight totalWeight .zeroCapacity .ratioOverflow
  .ok ({ state with lastBatchCount := batches }, batches)

/-- Apply a full-precision fractional capacity weight and cover any nonzero remainder. -/
@[pf_entry]
def prorateUp (state : State) (items weight totalWeight : UInt64) :
    Except Error (State × UInt64) := do
  let batches ← Math.UInt64.mulDivCeil items weight totalWeight .zeroCapacity .ratioOverflow
  .ok ({ state with lastBatchCount := batches }, batches)

end Examples.BatchSizer
