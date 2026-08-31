import ProofForge

/-!
EVM consumer of shared bounded UInt64 math. Quote rounding owns its zero-tick error and state
transition independently from the SVM batch-sizing policy.
-/

namespace Examples.EvmPriceBand

open ProofForge.Core

structure State where
  lastQuote : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | zeroTick
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (initial : UInt64) : State :=
  { lastQuote := initial }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.lastQuote

@[pf_entry]
def lower (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.min left right

@[pf_entry]
def upper (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.max left right

@[pf_entry]
def midpoint (_state : State) (left right : UInt64) : UInt64 :=
  Math.UInt64.average left right

@[pf_entry]
def roundUp (state : State) (amount tick : UInt64) : Except Error (State × UInt64) := do
  let quote ← Math.UInt64.ceilDiv amount tick .zeroTick
  .ok ({ state with lastQuote := quote }, quote)

end Examples.EvmPriceBand
