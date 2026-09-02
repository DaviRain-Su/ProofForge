import Examples.Svm.BatchSizer
import Examples.Evm.EvmPriceBand
import ProofForge

/-!
Host truth tables plus live SVM/EVM extraction for the same allocation-free bounded, saturating,
integer-logarithm, and square-root component. The two consumers own different errors and state
fields; neither gains a target component operation.
-/

namespace Tests.CoreMathSpec

open ProofForge.Core
open Lean Elab Command

def u64Max : UInt64 := ~~~(0 : UInt64)

#guard Math.UInt64.min 3 9 == 3
#guard Math.UInt64.min 9 3 == 3
#guard Math.UInt64.max 3 9 == 9
#guard Math.UInt64.max 9 3 == 9
#guard Math.UInt64.average 0 0 == 0
#guard Math.UInt64.average 4 7 == 5
#guard Math.UInt64.average 0 u64Max == 9223372036854775807
#guard Math.UInt64.average u64Max u64Max == u64Max
#guard match Math.UInt64.ceilDiv 0 7 false with
  | .ok value => value == 0
  | _ => false
#guard match Math.UInt64.ceilDiv 9 4 false with
  | .ok value => value == 3
  | _ => false
#guard match Math.UInt64.ceilDiv u64Max 2 false with
  | .ok value => value == 9223372036854775808
  | _ => false
#guard match Math.UInt64.ceilDiv u64Max 1 false with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.ceilDiv 7 0 false with
  | .error false => true
  | _ => false
#guard Math.UInt64.saturatingAdd (u64Max - 1) 1 == u64Max
#guard Math.UInt64.saturatingAdd u64Max 1 == u64Max
#guard Math.UInt64.saturatingAdd 1 u64Max == u64Max
#guard Math.UInt64.saturatingSub 3 7 == 0
#guard Math.UInt64.saturatingSub u64Max 1 == u64Max - 1
#guard Math.UInt64.saturatingMul 0 u64Max == 0
#guard Math.UInt64.saturatingMul u64Max 0 == 0
#guard Math.UInt64.saturatingMul (u64Max / 2) 2 == u64Max - 1
#guard Math.UInt64.saturatingMul (u64Max / 2 + 1) 2 == u64Max
#guard Math.UInt64.log2 0 == 0
#guard Math.UInt64.log2 1 == 0
#guard Math.UInt64.log2 2 == 1
#guard Math.UInt64.log2 3 == 1
#guard Math.UInt64.log2 0x8000000000000000 == 63
#guard Math.UInt64.log2 u64Max == 63
#guard Math.UInt64.log10 0 == 0
#guard Math.UInt64.log10 9 == 0
#guard Math.UInt64.log10 10 == 1
#guard Math.UInt64.log10 9999999999999999999 == 18
#guard Math.UInt64.log10 10000000000000000000 == 19
#guard Math.UInt64.log10 u64Max == 19
#guard Math.UInt64.log256 0 == 0
#guard Math.UInt64.log256 255 == 0
#guard Math.UInt64.log256 256 == 1
#guard Math.UInt64.log256 u64Max == 7
#guard Math.UInt64.sqrt 0 == 0
#guard Math.UInt64.sqrt 1 == 1
#guard Math.UInt64.sqrt 2 == 1
#guard Math.UInt64.sqrt 3 == 1
#guard Math.UInt64.sqrt 4 == 2
#guard Math.UInt64.sqrt 15 == 3
#guard Math.UInt64.sqrt 16 == 4
#guard Math.UInt64.sqrt 17 == 4
#guard Math.UInt64.sqrt 18446744065119617025 == 4294967295
#guard Math.UInt64.sqrt u64Max == 4294967295
#guard Math.UInt64.log2Ceil 0 == 0
#guard Math.UInt64.log2Ceil 1 == 0
#guard Math.UInt64.log2Ceil 2 == 1
#guard Math.UInt64.log2Ceil 3 == 2
#guard Math.UInt64.log2Ceil 4 == 2
#guard Math.UInt64.log2Ceil u64Max == 64
#guard Math.UInt64.log10Ceil 0 == 0
#guard Math.UInt64.log10Ceil 1 == 0
#guard Math.UInt64.log10Ceil 9 == 1
#guard Math.UInt64.log10Ceil 10 == 1
#guard Math.UInt64.log10Ceil 11 == 2
#guard Math.UInt64.log10Ceil 10000000000000000000 == 19
#guard Math.UInt64.log10Ceil u64Max == 20
#guard Math.UInt64.log256Ceil 0 == 0
#guard Math.UInt64.log256Ceil 1 == 0
#guard Math.UInt64.log256Ceil 255 == 1
#guard Math.UInt64.log256Ceil 256 == 1
#guard Math.UInt64.log256Ceil 257 == 2
#guard Math.UInt64.log256Ceil u64Max == 8
#guard Math.UInt64.sqrtCeil 0 == 0
#guard Math.UInt64.sqrtCeil 1 == 1
#guard Math.UInt64.sqrtCeil 2 == 2
#guard Math.UInt64.sqrtCeil 3 == 2
#guard Math.UInt64.sqrtCeil 4 == 2
#guard Math.UInt64.sqrtCeil 15 == 4
#guard Math.UInt64.sqrtCeil 16 == 4
#guard Math.UInt64.sqrtCeil 17 == 5
#guard Math.UInt64.sqrtCeil 18446744065119617025 == 4294967295
#guard Math.UInt64.sqrtCeil 18446744065119617026 == 4294967296
#guard Math.UInt64.sqrtCeil u64Max == 4294967296
#guard match Math.UInt64.mulDiv 10 20 3 false true with
  | .ok value => value == 66
  | _ => false
#guard match Math.UInt64.mulDiv u64Max 2 2 false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDiv u64Max u64Max u64Max false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDiv u64Max u64Max (u64Max - 1) false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDiv ((1 : UInt64) <<< 63) 2 u64Max false true with
  | .ok value => value == 1
  | _ => false
#guard match Math.UInt64.mulDiv ((1 : UInt64) <<< 63) 2 1 false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDiv 7 9 0 false true with
  | .error false => true
  | _ => false
#guard match Math.UInt64.mulDivCeil 10 20 3 false true with
  | .ok value => value == 67
  | _ => false
#guard match Math.UInt64.mulDivCeil u64Max 2 2 false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDivCeil 6 15372286728091293013 5 false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDivCeil 7 9 0 false true with
  | .error false => true
  | _ => false
#guard match FixedPoint.UInt64.mulDown 150 25 100 1 2 with
  | .ok value => value == 37
  | _ => false
#guard match FixedPoint.UInt64.mulUp 150 25 100 1 2 with
  | .ok value => value == 38
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 30 100 1 2 3 with
  | .ok value => value == 336
  | _ => false
#guard match FixedPoint.UInt64.divUp 101 30 100 1 2 3 with
  | .ok value => value == 337
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 0 0 1 2 3 with
  | .error 1 => true
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 0 100 1 2 3 with
  | .error 2 => true
  | _ => false
#guard match FixedPoint.UInt64.mulDown u64Max u64Max 1 1 2 with
  | .error 2 => true
  | _ => false

private def mulDivSamples : List UInt64 :=
  [0, 1, 2, 3, 7, 31, 0xffffffff, 0x100000000,
    0x7fffffffffffffff, 0x8000000000000000, u64Max - 1, u64Max]

private def validMulDiv (left right denominator : UInt64) : Bool :=
  let result := Math.UInt64.mulDiv left right denominator false true
  if denominator == 0 then
    match result with
    | .error false => true
    | _ => false
  else
    let quotient := (left.toNat * right.toNat) / denominator.toNat
    if u64Max.toNat < quotient then
      match result with
      | .error true => true
      | _ => false
    else
      match result with
      | .ok value => value.toNat == quotient
      | _ => false

#guard mulDivSamples.all fun left =>
  mulDivSamples.all fun right =>
    mulDivSamples.all fun denominator => validMulDiv left right denominator

private def validMulDivCeil (left right denominator : UInt64) : Bool :=
  let result := Math.UInt64.mulDivCeil left right denominator false true
  if denominator == 0 then
    match result with
    | .error false => true
    | _ => false
  else
    let product := left.toNat * right.toNat
    let quotient := (product + denominator.toNat - 1) / denominator.toNat
    if u64Max.toNat < quotient then
      match result with
      | .error true => true
      | _ => false
    else
      match result with
      | .ok value => value.toNat == quotient
      | _ => false

#guard mulDivSamples.all fun left =>
  mulDivSamples.all fun right =>
    mulDivSamples.all fun denominator => validMulDivCeil left right denominator

private def validFloorRoot (value : UInt64) : Bool :=
  let root := Math.UInt64.sqrt value
  if value == 0 then root == 0
  else root ≤ value / root && value / (root + 1) < root + 1

#guard (List.range 4096).all fun value => validFloorRoot (UInt64.ofNat value)
#guard validFloorRoot 0x7fffffffffffffff
#guard validFloorRoot 0x8000000000000000
#guard validFloorRoot u64Max

private def validCeilRoot (value : UInt64) : Bool :=
  let root := Math.UInt64.sqrtCeil value
  if value == 0 then root == 0
  else
    let lower := root - 1
    lower * lower < value && (root == 4294967296 || value ≤ root * root)

#guard (List.range 4096).all fun value => validCeilRoot (UInt64.ofNat value)
#guard validCeilRoot 0x7fffffffffffffff
#guard validCeilRoot 0x8000000000000000
#guard validCeilRoot u64Max

open Examples.Svm.BatchSizer in
#guard (smaller (init 8) 11 4 == 4) && (larger (init 8) 11 4 == 11) &&
  (midpoint (init 8) 4 7 == 5) &&
  (match plan (init 8) u64Max 2 with
  | .ok (state, result) => state.lastBatchCount == 9223372036854775808 &&
      result == state.lastBatchCount
  | _ => false) &&
  (match plan (init 8) 7 0 with
  | .error .zeroCapacity => true
  | _ => false) &&
  (match reserve (init (u64Max - 2)) 5 with
  | .ok (state, result) => state.lastBatchCount == u64Max && result == u64Max
  | _ => false) &&
  (match consume (init 3) 5 with
  | .ok (state, result) => state.lastBatchCount == 0 && result == 0
  | _ => false) &&
  (match amplify (init (u64Max / 2 + 1)) 2 with
  | .ok (state, result) => state.lastBatchCount == u64Max && result == u64Max
  | _ => false) &&
  binaryOrder (init 8) 65535 == 15 && decimalOrder (init 8) 1000000 == 6 &&
  byteOrder (init 8) 0x100000000 == 4 && capacityRoot (init 8) 1000000 == 1000 &&
  binaryOrderUp (init 8) 65535 == 16 && decimalOrderUp (init 8) 1000001 == 7 &&
  byteOrderUp (init 8) 0x100000001 == 5 && capacityRootUp (init 8) 1000001 == 1001 &&
  (match prorate (init 8) u64Max 2 2 with
  | .ok (state, result) => state.lastBatchCount == u64Max && result == u64Max
  | _ => false) &&
  (match prorate (init 8) ((1 : UInt64) <<< 63) 2 1 with
  | .error .ratioOverflow => true
  | _ => false) &&
  (match prorateUp (init 8) 10 20 3 with
  | .ok (state, result) => state.lastBatchCount == 67 && result == 67
  | _ => false) &&
  (match prorateUp (init 8) 6 15372286728091293013 5 with
  | .error .ratioOverflow => true
  | _ => false) &&
  (match fixedMulDown (init 8) 150 25 100 with
  | .ok (state, result) => state.lastBatchCount == 37 && result == 37
  | _ => false) &&
  (match fixedMulUp (init 8) 150 25 100 with
  | .ok (state, result) => state.lastBatchCount == 38 && result == 38
  | _ => false) &&
  (match fixedDivDown (init 8) 101 30 100 with
  | .ok (state, result) => state.lastBatchCount == 336 && result == 336
  | _ => false) &&
  (match fixedDivUp (init 8) 101 30 100 with
  | .ok (state, result) => state.lastBatchCount == 337 && result == 337
  | _ => false) &&
  (match fixedDivDown (init 8) 101 0 100 with
  | .error .zeroRate => true
  | _ => false)

open Examples.Evm.EvmPriceBand in
#guard (lower (init 9) 13 5 == 5) && (upper (init 9) 13 5 == 13) &&
  (midpoint (init 9) 0 u64Max == 9223372036854775807) &&
  (match roundUp (init 9) u64Max 1 with
  | .ok (state, result) => state.lastQuote == u64Max && result == state.lastQuote
  | _ => false) &&
  (match roundUp (init 9) 7 0 with
  | .error .zeroTick => true
  | _ => false) &&
  (match increase (init (u64Max - 2)) 5 with
  | .ok (state, result) => state.lastQuote == u64Max && result == u64Max
  | _ => false) &&
  (match discount (init 3) 5 with
  | .ok (state, result) => state.lastQuote == 0 && result == 0
  | _ => false) &&
  (match scale (init (u64Max / 2 + 1)) 2 with
  | .ok (state, result) => state.lastQuote == u64Max && result == u64Max
  | _ => false) &&
  binaryBand (init 9) u64Max == 63 && decimalBand (init 9) u64Max == 19 &&
  byteBand (init 9) u64Max == 7 && quoteRoot (init 9) u64Max == 4294967295 &&
  binaryBandUp (init 9) u64Max == 64 && decimalBandUp (init 9) u64Max == 20 &&
  byteBandUp (init 9) u64Max == 8 && quoteRootUp (init 9) u64Max == 4294967296 &&
  (match weighted (init 9) u64Max 2 2 with
  | .ok (state, result) => state.lastQuote == u64Max && result == u64Max
  | _ => false) &&
  (match weighted (init 9) ((1 : UInt64) <<< 63) 2 1 with
  | .error .quoteOverflow => true
  | _ => false) &&
  (match weightedUp (init 9) 10 20 3 with
  | .ok (state, result) => state.lastQuote == 67 && result == 67
  | _ => false) &&
  (match weightedUp (init 9) 6 15372286728091293013 5 with
  | .error .quoteOverflow => true
  | _ => false) &&
  (match fixedMulDown (init 9) 150 25 100 with
  | .ok (state, result) => state.lastQuote == 37 && result == 37
  | _ => false) &&
  (match fixedMulUp (init 9) 150 25 100 with
  | .ok (state, result) => state.lastQuote == 38 && result == 38
  | _ => false) &&
  (match fixedDivDown (init 9) 101 30 100 with
  | .ok (state, result) => state.lastQuote == 336 && result == 336
  | _ => false) &&
  (match fixedDivUp (init 9) 101 30 100 with
  | .ok (state, result) => state.lastQuote == 337 && result == 337
  | _ => false) &&
  (match fixedDivDown (init 9) 101 0 100 with
  | .error .zeroRate => true
  | _ => false)

/-- Pure shared math stays in ordinary target-neutral scalar Ops. -/
private partial def noTargetEffects (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.all fun
    | .ext _ => false
    | .ite _ _ _ yes no => noTargetEffects yes && noTargetEffects no
    | .forBody _ body => noTargetEffects body
    | _ => true

private def isUpper : ProofForge.Extract.IR.Val → Bool
  | .bitNot (.lit 0) => true
  | _ => false

/-- The unsafe arithmetic node must remain inside the exact preflight select that proves it fits. -/
private def isSaturatingAdd : ProofForge.Extract.IR.Val → Bool
  | .select .lt (.subU64 upper left) right capped (.addU64 addLeft addRight) =>
      isUpper upper && capped == upper && addLeft == left && addRight == right
  | _ => false

private def isSaturatingSub : ProofForge.Extract.IR.Val → Bool
  | .select .lt left right (.lit 0) (.subU64 subLeft subRight) =>
      subLeft == left && subRight == right
  | _ => false

private def isSaturatingMul : ProofForge.Extract.IR.Val → Bool
  | .select .lt (.lit 0) left
      (.select .lt (.divU64 upper divisor) right capped (.mulU64 mulLeft mulRight))
      (.lit 0) =>
      isUpper upper && divisor == left && capped == upper &&
        mulLeft == left && mulRight == right
  | _ => false

private partial def loopBounds (ops : Array ProofForge.Extract.IR.Op) : Array Nat :=
  ops.foldl (init := #[]) fun bounds op =>
    match op with
    | .ite _ _ _ yes no => bounds ++ loopBounds yes ++ loopBounds no
    | .forBody bound body => bounds.push bound ++ loopBounds body
    | _ => bounds

private partial def noAccumLoop (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.all fun
    | .forAccum .. => false
    | .ite _ _ _ yes no => noAccumLoop yes && noAccumLoop no
    | .forBody _ body => noAccumLoop body
    | _ => true

private def methodValue? (program : ProofForge.Extract.IR.Program) (name : String) :
    Option ProofForge.Extract.IR.Val := do
  let method ← program.methods.find? (·.ixName == name)
  method.ops.findSome? fun
    | .letLocal 0 value => some value
    | .returnU64 value => some value
    | _ => none

elab "#pf_guard_core_math_no_effects" : command => do
  let env ← getEnv
  for module in [`Examples.Svm.BatchSizer, `Examples.Evm.EvmPriceBand] do
    let source ←
      match ProofForge.Extract.extractModuleIR env module with
      | .ok program => pure program
      | .error reason => throwError reason
    for method in source.methods do
      unless noTargetEffects method.ops do
        throwError s!"{module}.{method.ixName}: shared math unexpectedly emitted a target effect"
    let checks : Array (String × (ProofForge.Extract.IR.Val → Bool)) :=
      if module == `Examples.Svm.BatchSizer then
        #[⟨"reserve", isSaturatingAdd⟩, ⟨"consume", isSaturatingSub⟩,
          ⟨"amplify", isSaturatingMul⟩]
      else
        #[⟨"increase", isSaturatingAdd⟩, ⟨"discount", isSaturatingSub⟩,
          ⟨"scale", isSaturatingMul⟩]
    for (name, valid) in checks do
      unless (methodValue? source name).any valid do
        throwError s!"{module}.{name}: saturating preflight no longer dominates its arithmetic"
    let logNames : Array (String × Nat) :=
      if module == `Examples.Svm.BatchSizer then
        #[⟨"binaryOrder", 6⟩, ⟨"decimalOrder", 5⟩, ⟨"byteOrder", 7⟩,
          ⟨"binaryOrderUp", 6⟩, ⟨"decimalOrderUp", 5⟩, ⟨"byteOrderUp", 7⟩]
      else
        #[⟨"binaryBand", 6⟩, ⟨"decimalBand", 5⟩, ⟨"byteBand", 7⟩,
          ⟨"binaryBandUp", 6⟩, ⟨"decimalBandUp", 5⟩, ⟨"byteBandUp", 7⟩]
    for (name, expectedBound) in logNames do
      let some method := source.methods.find? (·.ixName == name)
        | throwError s!"{module}.{name}: missing integer-log consumer"
      unless loopBounds method.ops == #[expectedBound] do
        throwError s!"{module}.{name}: expected exactly one {expectedBound}-step bounded ladder"
    let rootNames : Array String :=
      if module == `Examples.Svm.BatchSizer then #["capacityRoot", "capacityRootUp"]
      else #["quoteRoot", "quoteRootUp"]
    for rootName in rootNames do
      let some root := source.methods.find? (·.ixName == rootName)
        | throwError s!"{module}.{rootName}: missing integer-square-root consumer"
      unless loopBounds root.ops == #[5, 6] do
        throwError s!"{module}.{rootName}: expected exact five-step seed and six-step Newton ladders"
      unless noAccumLoop root.ops do
        throwError s!"{module}.{rootName}: Newton state was incorrectly lowered as additive accumulation"
    let mulDivNames : Array String :=
      if module == `Examples.Svm.BatchSizer then
        #["prorate", "prorateUp", "fixedMulDown", "fixedMulUp", "fixedDivDown", "fixedDivUp"]
      else
        #["weighted", "weightedUp", "fixedMulDown", "fixedMulUp", "fixedDivDown", "fixedDivUp"]
    for mulDivName in mulDivNames do
      let some mulDiv := source.methods.find? (·.ixName == mulDivName)
        | throwError s!"{module}.{mulDivName}: missing full-precision multiply/divide consumer"
      unless loopBounds mulDiv.ops == #[64] do
        throwError s!"{module}.{mulDivName}: expected exact 64-step restoring-division frame"
      unless noAccumLoop mulDiv.ops do
        throwError s!"{module}.{mulDivName}: restoring division was incorrectly lowered as accumulation"

#pf_guard_core_math_no_effects
#pf_build Examples.Svm.BatchSizer
#pf_evm_build Examples.Evm.EvmPriceBand

end Tests.CoreMathSpec
