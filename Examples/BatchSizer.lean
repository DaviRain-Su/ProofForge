import ProofForge

/-!
SVM consumer of shared bounded UInt64 math. Batch sizing owns its zero-capacity error and state
transition while min/max/average/ceilDiv remain target-neutral pure policy.
-/

namespace Examples.BatchSizer

open ProofForge.Core

structure State where
  lastBatchCount : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | zeroCapacity
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

end Examples.BatchSizer
