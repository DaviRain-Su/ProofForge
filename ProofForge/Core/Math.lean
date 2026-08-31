import ProofForge.Attr

namespace ProofForge.Core.Math.UInt64

/-!
# Allocation-free bounded UInt64 math

These helpers are target-neutral ordinary Lean policy. They use only existing scalar comparisons,
bit operations, and arithmetic, so SVM and EVM consumers share laws without sharing a physical
ABI, storage layout, Runtime effect, or emitter recipe.
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

end ProofForge.Core.Math.UInt64
