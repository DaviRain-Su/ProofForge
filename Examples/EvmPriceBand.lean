import ProofForge

/-!
EVM consumer of shared bounded UInt64 math. Quote rounding owns its zero-tick error and state
transition independently from the SVM batch-sizing and saturating-capacity policy.
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

/-- A quote increase clamps at the ABI/storage width instead of reverting. -/
@[pf_entry]
def increase (state : State) (amount : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingAdd state.lastQuote amount
  .ok ({ state with lastQuote := next }, next)

/-- A discount larger than the quote floors the quote to zero. -/
@[pf_entry]
def discount (state : State) (amount : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingSub state.lastQuote amount
  .ok ({ state with lastQuote := next }, next)

/-- Quote scaling clamps at the representable ABI/storage ceiling. -/
@[pf_entry]
def scale (state : State) (factor : UInt64) : Except Error (State × UInt64) :=
  let next := Math.UInt64.saturatingMul state.lastQuote factor
  .ok ({ state with lastQuote := next }, next)

end Examples.EvmPriceBand
