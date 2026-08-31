import Examples.BatchSizer
import Examples.EvmPriceBand
import ProofForge

/-!
Host truth tables plus live SVM/EVM extraction for the same allocation-free bounded/saturating
math component. The two consumers own different errors and state fields; neither gains a target
component operation.
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

open Examples.BatchSizer in
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
  | _ => false)

open Examples.EvmPriceBand in
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

private def methodValue? (program : ProofForge.Extract.IR.Program) (name : String) :
    Option ProofForge.Extract.IR.Val := do
  let method ← program.methods.find? (·.ixName == name)
  method.ops.findSome? fun
    | .letLocal 0 value => some value
    | _ => none

elab "#pf_guard_core_math_no_effects" : command => do
  let env ← getEnv
  for module in [`Examples.BatchSizer, `Examples.EvmPriceBand] do
    let source ←
      match ProofForge.Extract.extractModuleIR env module with
      | .ok program => pure program
      | .error reason => throwError reason
    for method in source.methods do
      unless noTargetEffects method.ops do
        throwError s!"{module}.{method.ixName}: shared math unexpectedly emitted a target effect"
    let checks : Array (String × (ProofForge.Extract.IR.Val → Bool)) :=
      if module == `Examples.BatchSizer then
        #[⟨"reserve", isSaturatingAdd⟩, ⟨"consume", isSaturatingSub⟩,
          ⟨"amplify", isSaturatingMul⟩]
      else
        #[⟨"increase", isSaturatingAdd⟩, ⟨"discount", isSaturatingSub⟩,
          ⟨"scale", isSaturatingMul⟩]
    for (name, valid) in checks do
      unless (methodValue? source name).any valid do
        throwError s!"{module}.{name}: saturating preflight no longer dominates its arithmetic"

#pf_guard_core_math_no_effects
#pf_build Examples.BatchSizer
#pf_evm_build Examples.EvmPriceBand

end Tests.CoreMathSpec
