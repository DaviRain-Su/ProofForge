import ProofForge.Attr
import ProofForge.Core.Math

namespace ProofForge.Core.FixedPoint.UInt64

/-!
# Allocation-free scaled UInt64 arithmetic

These helpers give SVM and EVM policy code one explicit fixed-point vocabulary over an
application-selected nonzero scale. They reuse `Core.Math.UInt64`'s exact 128-bit intermediate and
bounded restoring division; this module adds no target effect, physical representation, heap
value, or emitter recipe.
-/

/-- Floor of `(left * right) / scale`. A zero scale and an unrepresentable result use distinct
caller-owned errors. -/
@[pf_inline] def mulDown (left right scale : UInt64) (invalidScale overflow : ε) : Except ε UInt64 :=
  if scale == 0 then
    .error invalidScale
  else
    Math.UInt64.mulDiv left right scale invalidScale overflow

/-- Ceiling of `(left * right) / scale`. -/
@[pf_inline] def mulUp (left right scale : UInt64) (invalidScale overflow : ε) : Except ε UInt64 :=
  if scale == 0 then
    .error invalidScale
  else
    Math.UInt64.mulDivCeil left right scale invalidScale overflow

/-- Floor of `(value * scale) / divisor`. Scale validity is checked before the independently
caller-owned zero-divisor and overflow policies. -/
@[pf_inline] def divDown (value divisor scale : UInt64)
    (invalidScale divisionByZero overflow : ε) : Except ε UInt64 :=
  if scale == 0 then
    .error invalidScale
  else
    Math.UInt64.mulDiv value scale divisor divisionByZero overflow

/-- Ceiling of `(value * scale) / divisor`. -/
@[pf_inline] def divUp (value divisor scale : UInt64)
    (invalidScale divisionByZero overflow : ε) : Except ε UInt64 :=
  if scale == 0 then
    .error invalidScale
  else
    Math.UInt64.mulDivCeil value scale divisor divisionByZero overflow

end ProofForge.Core.FixedPoint.UInt64
