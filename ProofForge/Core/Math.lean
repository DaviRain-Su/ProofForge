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

/-- Floor of the integer square root. The nontrivial branch derives a power-of-two estimate from
the UInt64 magnitude, improves it to three halves of that estimate, then runs six bounded Newton
steps. The final division-based correction avoids squaring an intermediate estimate. -/
@[pf_inline] def sqrt (input : UInt64) : UInt64 :=
  if input ≤ 1 then
    input
  else Id.run do
    let mut value := input
    let mut estimate : UInt64 := 1
    for i in [0:5] do
      let shift := (32 : UInt64) >>> UInt64.ofNat i
      if 0 < value >>> shift then
        value := value >>> shift
        estimate := estimate <<< (shift >>> 1)
    estimate := (estimate * 3) >>> 1
    let mut quotient := input / estimate
    for _ in [0:6] do
      estimate := (estimate + quotient) >>> 1
      quotient := input / estimate
    return min estimate quotient

/-- Ceiling of the base-2 logarithm, returning zero for zero. For positive values above one,
`⌈log₂ input⌉ = ⌊log₂ (input - 1)⌋ + 1`; the guarded subtraction avoids powers and overflow. -/
@[pf_inline] def log2Ceil (input : UInt64) : UInt64 :=
  Id.run do
    let mut value := if input == 0 then 0 else input - 1
    let mut result : UInt64 := 0
    for i in [0:6] do
      let shift := (32 : UInt64) >>> UInt64.ofNat i
      if 0 < value >>> shift then
        value := value >>> shift
        result := result ||| shift
    return result + if input ≤ 1 then 0 else 1

/-- Ceiling of the base-10 logarithm, returning zero for zero. -/
@[pf_inline] def log10Ceil (input : UInt64) : UInt64 :=
  Id.run do
    let mut value := if input == 0 then 0 else input - 1
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
    return result + if input ≤ 1 then 0 else 1

/-- Ceiling of the base-256 logarithm, returning zero for zero. -/
@[pf_inline] def log256Ceil (input : UInt64) : UInt64 :=
  Id.run do
    let mut value := if input == 0 then 0 else input - 1
    let mut result : UInt64 := 0
    for _ in [0:7] do
      if 0xff < value then
        value := value >>> 8
        result := result + 1
    return result + if input ≤ 1 then 0 else 1

/-- Ceiling of the integer square root. For positive inputs,
`⌈√input⌉ = ⌊√(input - 1)⌋ + 1`; this avoids squaring the floor result. -/
@[pf_inline] def sqrtCeil (input : UInt64) : UInt64 :=
  if input == 0 then
    0
  else
    let predecessor := input - 1
    if predecessor ≤ 1 then
      predecessor + 1
    else Id.run do
      let mut value := predecessor
      let mut estimate : UInt64 := 1
      for i in [0:5] do
        let shift := (32 : UInt64) >>> UInt64.ofNat i
        if 0 < value >>> shift then
          value := value >>> shift
          estimate := estimate <<< (shift >>> 1)
      estimate := (estimate * 3) >>> 1
      let mut quotient := predecessor / estimate
      for _ in [0:6] do
        estimate := (estimate + quotient) >>> 1
        quotient := predecessor / estimate
      return min estimate quotient + 1

@[pf_inline] private def mulDivRounded (left right denominator : UInt64) (roundUp : Bool)
    (divisionByZero overflow : ε) : Except ε UInt64 :=
  if denominator == 0 then
    .error divisionByZero
  else
    let mask : UInt64 := 0xffffffff
    let leftLow := left &&& mask
    let leftHigh := left >>> 32
    let rightLow := right &&& mask
    let rightHigh := right >>> 32
    let lowLow := leftLow * rightLow
    let lowHigh := leftLow * rightHigh
    let highLow := leftHigh * rightLow
    let highHigh := leftHigh * rightHigh
    let middle := (lowLow >>> 32) + (lowHigh &&& mask) + (highLow &&& mask)
    let productLow := (lowLow &&& mask) ||| ((middle &&& mask) <<< 32)
    let productHigh :=
      highHigh + (lowHigh >>> 32) + (highLow >>> 32) + (middle >>> 32)
    if denominator ≤ productHigh then
      .error overflow
    else Id.run do
        let upper := ~~~(0 : UInt64)
        let complement := upper - denominator + 1
        let mut remainder := productHigh
        let mut quotient : UInt64 := 0
        for i in [0:64] do
          let shift := (63 : UInt64) - UInt64.ofNat i
          let bit := (productLow >>> shift) &&& 1
          let carry := remainder >>> 63
          let shifted := (remainder <<< 1) ||| bit
          quotient := quotient <<< 1
          if 0 < carry then
            remainder := shifted + complement
            quotient := quotient ||| 1
          else if denominator ≤ shifted then
            remainder := shifted - denominator
            quotient := quotient ||| 1
          else
            remainder := shifted
        if roundUp && 0 < remainder then
          if quotient == upper then
            return .error overflow
          else
            return .ok (quotient + 1)
        else
          return .ok quotient

/-- Floor of `(left * right) / denominator` with a full 128-bit intermediate product.

The two caller-owned errors distinguish a zero denominator from a quotient that does not fit in
UInt64. Multiplication is split into four 32-bit partial products, then a fixed 64-step restoring
division consumes the low product word with the high word as its initial remainder. The
`denominator ≤ high` preflight is exactly the floor-quotient overflow condition. No target needs a
wide integer opcode, heap value, or hidden wrapping arithmetic. -/
@[pf_inline] def mulDiv (left right denominator : UInt64)
    (divisionByZero overflow : ε) : Except ε UInt64 :=
  mulDivRounded left right denominator false divisionByZero overflow

/-- Ceiling of `(left * right) / denominator` with the same exact 128-bit product and restoring
division as `mulDiv`. A nonzero remainder increments the quotient only after checking that the
rounded result remains representable. -/
@[pf_inline] def mulDivCeil (left right denominator : UInt64)
    (divisionByZero overflow : ε) : Except ε UInt64 :=
  mulDivRounded left right denominator true divisionByZero overflow

end ProofForge.Core.Math.UInt64
