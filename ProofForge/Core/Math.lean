import ProofForge.Attr

namespace ProofForge.Core.Math.UInt64

/-!
# Allocation-free bounded UInt64 math

These helpers are target-neutral ordinary Lean policy. They use only existing scalar comparisons,
bit operations, arithmetic, and statically bounded loops, so SVM and EVM consumers share laws
without sharing a physical ABI, storage layout, Runtime effect, or emitter recipe.
-/

/-- The smaller operand. -/
@[pf_inline] def min (left right : UInt64) : UInt64 :=
  if left < right then left else right

/-- The larger operand. -/
@[pf_inline] def max (left right : UInt64) : UInt64 :=
  if left < right then right else left

/-- Floor of the arithmetic mean without overflowing the intermediate sum. This is the standard
bitwise identity `(a & b) + ((a ^ b) / 2)`. -/
@[pf_inline] def average (left right : UInt64) : UInt64 :=
  (left &&& right) + ((left ^^^ right) >>> 1)

/-- Ceiling division with an explicit caller-owned zero-denominator error. The nonzero branch uses
`0` for a zero numerator and otherwise `(numerator - 1) / denominator + 1`; both intermediate
operations are representable under those branch conditions. -/
@[pf_inline] def ceilDiv (numerator denominator : UInt64) (error : ε) : Except ε UInt64 :=
  if denominator == 0 then
    .error error
  else if numerator == 0 then
    .ok 0
  else
    .ok ((numerator - 1) / denominator + 1)

/-- Addition bounded to the maximum UInt64 value instead of failing on overflow. The subtraction
in the preflight is always representable, and the checked addition is reached only when it fits. -/
@[pf_inline] def saturatingAdd (left right : UInt64) : UInt64 :=
  let upper := ~~~(0 : UInt64)
  if upper - left < right then upper else left + right

/-- Subtraction bounded to zero instead of failing on underflow. -/
@[pf_inline] def saturatingSub (left right : UInt64) : UInt64 :=
  if left < right then 0 else left - right

/-- Multiplication bounded to the maximum UInt64 value instead of failing on overflow. The zero
branch guards division; otherwise `upper / left` exactly preflights the checked product. -/
@[pf_inline] def saturatingMul (left right : UInt64) : UInt64 :=
  if 0 < left then
    let upper := ~~~(0 : UInt64)
    if upper / left < right then upper else left * right
  else
    0

/-- Floor of the base-2 logarithm, returning zero for zero. The fixed six-stage ladder is the
UInt64 specialization of a most-significant-bit search; every shift is bounded by 32. -/
@[pf_inline] def log2 (input : UInt64) : UInt64 := Id.run do
  let mut value := input
  let mut result : UInt64 := 0
  for i in [0:6] do
    let shift := (32 : UInt64) >>> UInt64.ofNat i
    if 0 < value >>> shift then
      value := value >>> shift
      result := result ||| shift
  return result

/-- Floor of the base-10 logarithm, returning zero for zero. The fixed decimal ladder reduces the
operand by powers 10^16, 10^8, 10^4, 10^2, and 10 without allocation or an unbounded loop. -/
@[pf_inline] def log10 (input : UInt64) : UInt64 := Id.run do
  let mut value := input
  let mut result : UInt64 := 0
  for i in [0:5] do
    let divisor : UInt64 :=
      if i == 0 then 10000000000000000
      else if i == 1 then 100000000
      else if i == 2 then 10000
      else if i == 3 then 100
      else 10
    if divisor ≤ value then
      value := value / divisor
      result := result ||| ((16 : UInt64) >>> UInt64.ofNat i)
  return result

/-- Floor of the base-256 logarithm, returning zero for zero. This is the zero-based index of the
highest nonzero byte and therefore the floor base-2 logarithm divided by eight. -/
@[pf_inline] def log256 (input : UInt64) : UInt64 := Id.run do
  let mut value := input
  let mut result : UInt64 := 0
  for _ in [0:7] do
    if 0xff < value then
      value := value >>> 8
      result := result + 1
  return result

end ProofForge.Core.Math.UInt64
