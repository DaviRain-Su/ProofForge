import ProofForge.Core.Codec

/-!
# NEAR boundary codec plans

Target-owned canonical Borsh geometry for the first bounded byte/string entry slice. The source
carrier is a fixed scalar frame (`UInt32` length plus `capacity` UInt8 slots); NEAR wire input is
the canonical `u32_le length || active bytes` prefix. No source Vector or target pointer survives.
-/

namespace ProofForge.Wasm.Near.Codec

/-- Bound generated scalar locals and linear-memory work while retaining useful AccountId-sized
payloads. This is a ProofForge compilation limit, not a Borsh or nearcore protocol limit. -/
def maxBoundedBytesCapacity : Nat := 64

structure BorshInputPlan where
  capacity : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

def BorshInputPlan.localCount (plan : BorshInputPlan) : Nat := 1 + plan.capacity

def BorshInputPlan.canonical (plan : BorshInputPlan) : String :=
  s!"near-borsh-{if plan.validateUtf8 then "string" else "bytes"}-v1(capacity={plan.capacity})"

def inputPlan : Core.Codec.Schema → Except String BorshInputPlan
  | .boundedBytes capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedBytesCapacity do
        throw s!"near/codec: bounded bytes capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := false }
  | .boundedString capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedBytesCapacity do
        throw s!"near/codec: bounded string capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := true }
  | _ => throw "near/codec: input plan requires bounded bytes or string"

def BorshInputPlan.valueIndex? (plan : BorshInputPlan) (name : String) : Option Nat := do
  unless name.startsWith "values_" do none
  let index ← (name.drop 7).toNat?
  if index < plan.capacity then some index else none

end ProofForge.Wasm.Near.Codec
