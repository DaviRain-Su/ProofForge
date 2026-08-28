import ProofForge.Core.Codec

namespace ProofForge.Evm.Codec

open ProofForge.Core.Codec

/-- Decode the legacy width sentinels at one compatibility boundary.  New EVM
code consumes `Scalar` and must not interpret these numbers itself. -/
def scalarOfLegacyWidth : Nat → Except String Scalar
  | 1 => pure .uint8
  | 2 => pure .uint16
  | 4 => pure .uint32
  | 8 => pure .uint64
  | 20 => pure .address20
  | 32 => pure .uint256
  | 33 => pure .bytes32
  | width => throw s!"evm/codec: unsupported legacy width {width}"

def legacyWidthOfScalar : Scalar → Except String Nat
  | .boolean => throw "evm/codec: boolean has no legacy width"
  | .uint 8 => pure 1
  | .uint 16 => pure 2
  | .uint 32 => pure 4
  | .uint 64 => pure 8
  | .uint 256 => pure 32
  | .address 20 => pure 20
  | .fixedBytes 32 => pure 33
  | type => throw s!"evm/codec: no legacy width for {repr type}"

def abiType : Scalar → Except String String
  | .boolean => pure "bool"
  | .uint bits =>
      if Scalar.isWellFormed (.uint bits) then pure s!"uint{bits}"
      else throw s!"evm/codec: invalid uint width {bits}"
  | .address 20 => pure "address"
  | .address bytes => throw s!"evm/codec: address must be 20 bytes, got {bytes}"
  | .fixedBytes bytes =>
      if 1 ≤ bytes && bytes ≤ 32 then pure s!"bytes{bytes}"
      else throw s!"evm/codec: invalid fixed-bytes width {bytes}"

def limbCount : Scalar → Nat
  | .uint bits => (bits + 63) / 64
  | .address bytes | .fixedBytes bytes => (bytes + 7) / 8
  | .boolean => 1

private def abiPartIndex : String → Option Nat
  | "w0" => some 0
  | "w1" => some 1
  | "w2" => some 2
  | "w3" => some 3
  | _ => none

private partial def abiTypeOfSchemaAt : Schema → Except String String
  | .unit => throw "evm/codec: unit has no canonical ABI parameter type"
  | .scalar type => abiType type
  | .tuple items => do
      if items.isEmpty then throw "evm/codec: empty tuple is not supported"
      let types ← items.mapM abiTypeOfSchemaAt
      return "(" ++ String.intercalate "," types.toList ++ ")"
  | .record _ fields => do
      if fields.isEmpty then throw "evm/codec: empty record is not supported"
      let types ← fields.mapM fun field => abiTypeOfSchemaAt field.2
      return "(" ++ String.intercalate "," types.toList ++ ")"
  | .fixedArray length element => do
      if length == 0 then throw "evm/codec: zero-length fixed array is not supported"
      return (← abiTypeOfSchemaAt element) ++ "[" ++ toString length ++ "]"
  | .enumeration .. => throw "evm/codec: enum ABI tags require an explicit target policy"
  | .option _ => throw "evm/codec: option ABI tags require an explicit target policy"
  | .boundedArray .. => throw "evm/codec: bounded arrays require an explicit dynamic ABI policy"

/-- Canonical Solidity ABI spelling for one logical parameter or result. Nested records and Lean
products are tuples; literal vectors are fixed arrays. This target-owned function deliberately
does not expose ABI words or padding to Core. -/
def abiTypeOfSchema (schema : Schema) : Except String String := do
  let _ ← validate schema
  abiTypeOfSchemaAt schema

/-- One ABI word per statically present scalar leaf. Wide source values still occupy one ABI word;
their fixed source limbs are unpacked only when an operation projects `w0`..`w3`. -/
def staticAbiLeaves (schema : Schema) : Except String (Array StaticLeaf) := do
  let _ ← abiTypeOfSchema schema
  staticLeaves schema

/-- One source projection into the physical words of an EVM input parameter. `wordIndex` is
relative to that logical parameter; `partCount` describes the fixed source limbs carried by the
single ABI word. -/
structure AbiProjection where
  sourceName : String
  wordIndex : Nat
  partCount : Nat
  deriving Repr, BEq, Inhabited

/-- Canonicality rule for one tag and its fixed payload lanes. Each variant activates a prefix of
the payload words; every inactive word must be zero. -/
structure TaggedGuard where
  tagWord : Nat
  payloadStart : Nat
  payloadWords : Nat
  activePayloadWords : Array Nat
  deriving Repr, BEq, Inhabited

/-- Complete EVM-owned input plan for one logical parameter. It contains ABI words and tag guards,
but no storage slots, source Ops, or contract policy. -/
structure AbiInputPlan where
  typeName : String
  words : Array Scalar
  projections : Array AbiProjection
  taggedGuards : Array TaggedGuard := #[]
  deriving Repr, BEq, Inhabited

def AbiInputPlan.wordCount (plan : AbiInputPlan) : Nat := plan.words.size

/-- Canonical identity for guard semantics not visible in the Solidity selector. Two enums can
share the same fixed tuple type while activating different payload lanes, so target IR digests
must retain this policy identity. Static plans return the empty compatibility marker. -/
def AbiInputPlan.taggedCanonical (plan : AbiInputPlan) : String :=
  if plan.taggedGuards.isEmpty then ""
  else
    let guards := plan.taggedGuards.map fun guard =>
      let active := String.intercalate "," (guard.activePayloadWords.map toString).toList
      s!"{guard.tagWord}:{guard.payloadStart}:{guard.payloadWords}:[{active}]"
    "tagged-tuple-v1(" ++ plan.typeName ++ ";" ++
      String.intercalate "," guards.toList ++ ")"

private def staticInputPlan (schema : Schema) : Except String AbiInputPlan := do
  let leaves ← staticAbiLeaves schema
  return {
    typeName := ← abiTypeOfSchema schema
    words := leaves.map (·.type)
    projections := leaves.mapIdx fun wordIndex leaf => {
      sourceName := leaf.sourceName
      wordIndex
      partCount := limbCount leaf.type
    }
  }

private def enumPayloadWords : Schema → Except String Nat
  | .unit => pure 0
  | .scalar (.uint 64) => pure 1
  | .tuple items => do
      unless items.all (· == .scalar .uint64) do
        throw "evm/codec: tagged tuple v1 enum fields must be UInt64"
      return items.size
  | _ => throw "evm/codec: tagged tuple v1 enum fields must be UInt64"

/-- **ProofForge EVM Tagged Tuple v1** is the explicit standard-ABI input policy for logical sums.

* `Option<T>` is `(bool present,T value)`. An absent value requires every payload word to be zero.
* A payload enum is `(uint8 tag,uint64 p0,...)`, with enough lanes for its largest constructor.
  The tag is the source constructor ordinal and every lane inactive for that constructor is zero.

The fixed tuple avoids dynamic offsets and gives every source projection one bounded ABI word.
Tagged returns and dynamic tails are deliberately outside this input-only policy. -/
def taggedTupleV1InputPlan : Schema → Except String AbiInputPlan
  | .option payload => do
      let payloadPlan ← staticInputPlan payload
      unless !payloadPlan.words.isEmpty do
        throw "evm/codec: tagged tuple v1 Option payload must contain a scalar"
      let payloadProjections := payloadPlan.projections.map fun projection => {
        projection with
        sourceName := if projection.sourceName.isEmpty then "slot_p0"
          else "slot_p0_" ++ projection.sourceName
        wordIndex := 1 + projection.wordIndex
      }
      return {
        typeName := "(bool," ++ payloadPlan.typeName ++ ")"
        words := #[.boolean] ++ payloadPlan.words
        projections := #[{
          sourceName := "slot_tag"
          wordIndex := 0
          partCount := 1
        }] ++ payloadProjections
        taggedGuards := #[{
          tagWord := 0
          payloadStart := 1
          payloadWords := payloadPlan.wordCount
          activePayloadWords := #[0, payloadPlan.wordCount]
        }]
      }
  | .enumeration _ tagBits variants => do
      unless tagBits == 8 do
        throw "evm/codec: tagged tuple v1 enum tag must be uint8"
      unless !variants.isEmpty && variants.size ≤ 256 do
        throw "evm/codec: tagged tuple v1 enum variants must fit uint8"
      let counts ← variants.mapM fun variant => enumPayloadWords variant.2
      let payloadWords := counts.foldl (init := 0) max
      let mut projections : Array AbiProjection := #[{
        sourceName := "variant_tag"
        wordIndex := 0
        partCount := 1
      }]
      if payloadWords == 0 then
        projections := projections.push {
          sourceName := ""
          wordIndex := 0
          partCount := 1
        }
      else
        for i in [0:payloadWords] do
          projections := projections.push {
            sourceName := "variant_p" ++ toString i
            wordIndex := 1 + i
            partCount := 1
          }
      let types := #["uint8"] ++ Array.replicate payloadWords "uint64"
      return {
        typeName := "(" ++ String.intercalate "," types.toList ++ ")"
        words := #[.uint8] ++ Array.replicate payloadWords .uint64
        projections
        taggedGuards := #[{
          tagWord := 0
          payloadStart := 1
          payloadWords
          activePayloadWords := counts
        }]
      }
  | _ => throw "evm/codec: tagged tuple v1 requires Option or enum input"

/-- Select the EVM input policy once. Static schemas retain canonical Solidity ABI flattening;
logical sums opt into the explicitly named Tagged Tuple v1 policy above. -/
def inputPlan (schema : Schema) : Except String AbiInputPlan := do
  let _ ← validate schema
  match schema with
  | .option _ | .enumeration .. => taggedTupleV1InputPlan schema
  | .boundedArray .. => throw "evm/codec: bounded arrays require an explicit dynamic ABI policy"
  | _ => staticInputPlan schema

/-- Resolve Extract's compatibility projection spelling against one EVM input plan. -/
def AbiInputPlan.resolveProjection (plan : AbiInputPlan) (name : String) :
    Except String StaticProjection := do
  let mut found : Array StaticProjection := #[]
  for projection in plan.projections do
    if name == projection.sourceName && projection.partCount == 1 then
      found := found.push { leafIndex := projection.wordIndex, partIndex := 0 }
    else if projection.sourceName.isEmpty then
      if let some partIndex := abiPartIndex name then
        if partIndex < projection.partCount then
          found := found.push { leafIndex := projection.wordIndex, partIndex }
    else if name.startsWith (projection.sourceName ++ "_") then
      let suffix := name.drop (projection.sourceName.length + 1) |>.copy
      if let some partIndex := abiPartIndex suffix then
        if partIndex < projection.partCount then
          found := found.push { leafIndex := projection.wordIndex, partIndex }
  unless found.size == 1 do
    let shown := if name.isEmpty then "<parameter>" else name
    throw s!"evm/codec: input projection {shown} is missing or ambiguous"
  return found[0]!

inductive WordGuard where
  | boolean
  | unsignedMax (bits : Nat)
  | address160
  | fixedBytesLeftPadded (bytes : Nat)
  | fullWord
  deriving Repr, BEq, Inhabited

def wordGuard : Scalar → Except String WordGuard
  | .boolean => pure .boolean
  | .uint 256 => pure .fullWord
  | .uint bits =>
      if Scalar.isWellFormed (.uint bits) then pure (.unsignedMax bits)
      else throw s!"evm/codec: invalid uint width {bits}"
  | .address 20 => pure .address160
  | .address bytes => throw s!"evm/codec: address must be 20 bytes, got {bytes}"
  | .fixedBytes 32 => pure .fullWord
  | .fixedBytes bytes =>
      if 1 ≤ bytes && bytes < 32 then pure (.fixedBytesLeftPadded bytes)
      else throw s!"evm/codec: invalid fixed-bytes width {bytes}"

def isWideIntegerCarrier : Scalar → Bool
  | .uint bits => 64 < bits && bits ≤ 256 && bits % 64 == 0
  | _ => false

def isFixedBytesCarrier : Scalar → Bool
  | .fixedBytes bytes => 1 ≤ bytes && bytes ≤ 32
  | _ => false

def isAddressCarrier : Scalar → Bool
  | .address 20 => true
  | _ => false

def isNarrowIntegerCarrier : Scalar → Bool
  | .boolean => true
  | .uint bits => bits ≤ 64
  | _ => false

/-- EVM word mask for a physical byte width. Storage layout and calldata
guards share this target-owned rendering primitive. -/
private def ffBytes : Nat → String
  | 0 => ""
  | count + 1 => "ff" ++ ffBytes count

def byteMask (bytes : Nat) : String :=
  if bytes == 0 || bytes > 32 then "0" else "0x" ++ ffBytes bytes

end ProofForge.Evm.Codec
