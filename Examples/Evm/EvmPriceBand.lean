import ProofForge

/-!
EVM consumer of shared bounded UInt64 math. Quote rounding owns its zero-tick error and state
transition independently from the SVM batch-sizing and saturating-capacity policy.
-/

namespace Examples.Evm.EvmPriceBand
open ProofForge.Core

structure State where
  lastQuote : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | zeroTick
  | quoteOverflow
  | zeroRate
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

/-- Zero-based binary magnitude for quote band selection. -/
@[pf_entry]
def binaryBand (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log2 quote

/-- Zero-based decimal magnitude for quote decimal policy. -/
@[pf_entry]
def decimalBand (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log10 quote

/-- Zero-based highest occupied byte for compact quote encoding. -/
@[pf_entry]
def byteBand (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log256 quote

/-- Floor square root for quote normalization. -/
@[pf_entry]
def quoteRoot (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.sqrt quote

/-- First binary band whose power of two covers the quote. -/
@[pf_entry]
def binaryBandUp (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log2Ceil quote

/-- First decimal band whose power of ten covers the quote. -/
@[pf_entry]
def decimalBandUp (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log10Ceil quote

/-- First base-256 band whose power covers the quote. -/
@[pf_entry]
def byteBandUp (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.log256Ceil quote

/-- Smallest integral normalization root whose square covers the quote. -/
@[pf_entry]
def quoteRootUp (_state : State) (quote : UInt64) : UInt64 :=
  Math.UInt64.sqrtCeil quote

/-- Scale a quote by a rational weight using a full-width intermediate product. The EVM policy
owns its named zero-denominator and quotient-overflow errors independently from SVM. -/
@[pf_entry]
def weighted (state : State) (quote numerator denominator : UInt64) :
    Except Error (State × UInt64) := do
  let result ← Math.UInt64.mulDiv quote numerator denominator .zeroTick .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

/-- Scale a quote by a rational weight and round every nonzero remainder upward. -/
@[pf_entry]
def weightedUp (state : State) (quote numerator denominator : UInt64) :
    Except Error (State × UInt64) := do
  let result ← Math.UInt64.mulDivCeil quote numerator denominator .zeroTick .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

/-- Multiply scaled quotes with floor rounding. -/
@[pf_entry]
def fixedMulDown (state : State) (left right scale : UInt64) :
    Except Error (State × UInt64) := do
  let result ← FixedPoint.UInt64.mulDown left right scale .zeroTick .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

/-- Multiply scaled quotes with ceiling rounding. -/
@[pf_entry]
def fixedMulUp (state : State) (left right scale : UInt64) :
    Except Error (State × UInt64) := do
  let result ← FixedPoint.UInt64.mulUp left right scale .zeroTick .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

/-- Divide scaled quotes with floor rounding. -/
@[pf_entry]
def fixedDivDown (state : State) (value divisor scale : UInt64) :
    Except Error (State × UInt64) := do
  let result ← FixedPoint.UInt64.divDown value divisor scale .zeroTick .zeroRate .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

/-- Divide scaled quotes with ceiling rounding. -/
@[pf_entry]
def fixedDivUp (state : State) (value divisor scale : UInt64) :
    Except Error (State × UInt64) := do
  let result ← FixedPoint.UInt64.divUp value divisor scale .zeroTick .zeroRate .quoteOverflow
  .ok ({ state with lastQuote := result }, result)

end Examples.Evm.EvmPriceBand