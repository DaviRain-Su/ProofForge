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

/-- Raw storage keys, values, and copied register results reuse the bounded-byte compiler budget.
This is not nearcore's protocol limit. A capacity of at least one still represents an empty byte
sequence through runtime `length = 0`. -/
def storageCapacityValid (capacity : Nat) : Bool :=
  1 ≤ capacity && capacity ≤ maxBoundedBytesCapacity

structure BorshInputPlan where
  capacity : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

def BorshInputPlan.localCount (plan : BorshInputPlan) : Nat := 1 + plan.capacity

def BorshInputPlan.canonical (plan : BorshInputPlan) : String :=
  s!"near-borsh-{if plan.validateUtf8 then "string" else "bytes"}-v1(capacity={plan.capacity})"

def inputPlan : Core.Codec.Schema → Except String BorshInputPlan
  | .boundedBytes capacity => do
      unless storageCapacityValid capacity do
        throw s!"near/codec: bounded bytes capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := false }
  | .boundedString capacity => do
      unless storageCapacityValid capacity do
        throw s!"near/codec: bounded string capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := true }
  | _ => throw "near/codec: input plan requires bounded bytes or string"

def BorshInputPlan.valueIndex? (plan : BorshInputPlan) (name : String) : Option Nat := do
  unless name.startsWith "values_" do none
  let index ← (name.drop 7).toNat?
  if index < plan.capacity then some index else none

/-- Keep fixed return frames small enough for deterministic generated WAT. This is a compiler
resource bound, not a Borsh or nearcore wire limit. -/
def maxBoundedOutputCapacity : Nat := 64

inductive BorshOutputKind where
  | array
  | bytes
  | string
  deriving Repr, BEq, Inhabited

/-- Target-owned output geometry. Extract supplies `length, slot₀ … slotₙ₋₁`; the emitter publishes
only canonical `u32_le(length) || active elements` through invocation-local arena memory. -/
structure BorshOutputPlan where
  kind : BorshOutputKind
  capacity : Nat
  elementWidth : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

def BorshOutputPlan.sourceValueCount (plan : BorshOutputPlan) : Nat :=
  1 + plan.capacity

def BorshOutputPlan.maxBytes (plan : BorshOutputPlan) : Nat :=
  4 + plan.capacity * plan.elementWidth

def BorshOutputPlan.canonical (plan : BorshOutputPlan) : String :=
  let kind := match plan.kind with
    | .array => "array"
    | .bytes => "bytes"
    | .string => "string"
  s!"near-borsh-output-{kind}-v1(capacity={plan.capacity},width={plan.elementWidth})"

def outputPlan : Core.Codec.Schema → Except String BorshOutputPlan
  | .boundedArray capacity (.scalar (.uint bits)) => do
      let width := bits / 8
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      unless bits % 8 == 0 && (width == 1 || width == 2 || width == 4 || width == 8) do
        throw "near/codec: bounded output elements must be UInt8, UInt16, UInt32, or UInt64"
      pure { kind := .array, capacity, elementWidth := width, validateUtf8 := false }
  | .boundedBytes capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      pure { kind := .bytes, capacity, elementWidth := 1, validateUtf8 := false }
  | .boundedString capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      pure { kind := .string, capacity, elementWidth := 1, validateUtf8 := true }
  | .boundedArray .. =>
      throw "near/codec: bounded output elements must be UInt8, UInt16, UInt32, or UInt64"
  | _ => throw "near/codec: output plan requires bounded bytes, string, or scalar array"

end ProofForge.Wasm.Near.Codec
