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
  | .boundedBytes .. => throw "evm/codec: bounded bytes require an explicit dynamic ABI policy"
  | .boundedString .. => throw "evm/codec: bounded strings require an explicit dynamic ABI policy"

/-- Canonical Solidity ABI spelling for one logical parameter or result. Nested records and Lean
products are tuples; literal vectors are fixed arrays. This target-owned function deliberately
does not expose ABI words or padding to Core. -/
def abiTypeOfSchema (schema : Schema) : Except String String := do
  let _ ← validate schema
  match schema with
  | .boundedArray _ element =>
      return (← abiTypeOfSchemaAt element) ++ "[]"
  | .boundedBytes _ => pure "bytes"
  | .boundedString _ => pure "string"
  | _ => abiTypeOfSchemaAt schema

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

/-- Target-owned dynamic-tail geometry for a bounded top-level ABI array. `elementWords` describes
one statically shaped element; all `capacity` source slots still live in a fixed local frame. -/
structure BoundedArrayPlan where
  capacity : Nat
  elementWords : Array Scalar
  deriving Repr, BEq, Inhabited

/-- Target-owned dynamic-tail policy shared by standard ABI `bytes` and `string`. Both use packed
bytes on the wire; String additionally requires strict Unicode-scalar UTF-8 before source code can
observe the fixed local frame. -/
structure PackedBytesPlan where
  capacity : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

/-- One standard-ABI dynamic input policy. Keeping this as a sum prevents malformed plans from
claiming multiple incompatible tail geometries and gives the codec interpreter one extension
boundary for future dynamic shapes. -/
inductive DynamicInputPlan where
  | boundedArray (plan : BoundedArrayPlan)
  | packedBytes (plan : PackedBytesPlan)
  deriving Repr, BEq, Inhabited

/-- Output-side bounded-array geometry is intentionally distinct from calldata-tail geometry.
The source frame remains fixed, while the standard ABI result publishes only its active prefix. -/
structure BoundedArrayOutputPlan where
  capacity : Nat
  elementTypeName : String
  elementWords : Array Scalar
  deriving Repr, BEq, Inhabited

/-- Output-side packed bytes policy. String results are validated again at the publication
boundary, independently of any input validation that may have produced the source frame. -/
structure PackedBytesOutputPlan where
  capacity : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

/-- One standard-ABI dynamic output policy. It never reuses calldata offsets or cursor state. -/
inductive DynamicOutputPlan where
  | boundedArray (plan : BoundedArrayOutputPlan)
  | packedBytes (plan : PackedBytesOutputPlan)
  deriving Repr, BEq, Inhabited

/-- Output-side Tagged Tuple v1 geometry. It deliberately contains no calldata offsets,
input projections, or decoded guard state: returndata is rebuilt from the fixed shared source
frame and checked again at the publication boundary. -/
structure TaggedTupleOutputPlan where
  typeName : String
  words : Array Scalar
  activePayloadWords : Array Nat
  deriving Repr, BEq, Inhabited

/-- One EVM ABI output policy. Dynamic tails and fixed tagged tuples are disjoint variants so a
method cannot accidentally carry two incompatible return encoders. -/
inductive OutputPlan where
  | dynamic (plan : DynamicOutputPlan)
  | taggedTuple (plan : TaggedTupleOutputPlan)
  deriving Repr, BEq, Inhabited

/-- Fixed source-frame geometry shared by dynamic inputs that support scalar indexed reads. Wire
decoding remains variant-specific in the target codec interpreter. -/
def DynamicInputPlan.indexedFrame : DynamicInputPlan → Nat × Array Scalar
  | .boundedArray array => (array.capacity, array.elementWords)
  | .packedBytes bytes => (bytes.capacity, #[.uint8])

/-- Complete EVM-owned input plan for one logical parameter. It contains ABI words and tag guards,
but no storage slots, source Ops, or contract policy. -/
structure AbiInputPlan where
  typeName : String
  /-- Fixed source-local frame. A bounded dynamic array uses one length word followed by every
  compile-time element slot; this is intentionally distinct from its one-word ABI head. -/
  words : Array Scalar
  projections : Array AbiProjection
  taggedGuards : Array TaggedGuard := #[]
  dynamic : Option DynamicInputPlan := none
  deriving Repr, BEq, Inhabited

def AbiInputPlan.wordCount (plan : AbiInputPlan) : Nat := plan.words.size

def AbiInputPlan.headWordCount (plan : AbiInputPlan) : Nat :=
  if plan.dynamic.isSome then 1 else plan.wordCount

/-- Compatibility/query view for consumers that specifically need bounded-array element shape. -/
def AbiInputPlan.boundedArray (plan : AbiInputPlan) : Option BoundedArrayPlan :=
  match plan.dynamic with
  | some (.boundedArray array) => some array
  | _ => none

def AbiInputPlan.packedBytes (plan : AbiInputPlan) : Option PackedBytesPlan :=
  match plan.dynamic with
  | some (.packedBytes bytes) => some bytes
  | _ => none

/-- Fixed source-frame scalar metadata consumed by the output codec interpreter. -/
def DynamicOutputPlan.sourceWords : DynamicOutputPlan → Array Scalar
  | .boundedArray array =>
      #[.uint32] ++ (Array.range array.capacity).flatMap fun _ => array.elementWords
  | .packedBytes bytes => #[.uint32] ++ Array.replicate bytes.capacity .uint8

def TaggedTupleOutputPlan.sourceWords (plan : TaggedTupleOutputPlan) : Array Scalar :=
  plan.words

def OutputPlan.sourceWords : OutputPlan → Array Scalar
  | .dynamic plan => plan.sourceWords
  | .taggedTuple plan => plan.sourceWords

/-- Canonical identity for output rules that are not visible in a Solidity function selector. -/
def DynamicOutputPlan.canonical : DynamicOutputPlan → String
  | .boundedArray array =>
      s!"bounded-array-return-v1({array.elementTypeName}[];capacity={array.capacity};" ++
        s!"element-words={array.elementWords.size})"
  | .packedBytes bytes =>
      s!"packed-bytes-return-v1(capacity={bytes.capacity};utf8={bytes.validateUtf8})"

def TaggedTupleOutputPlan.canonical (plan : TaggedTupleOutputPlan) : String :=
  let active := String.intercalate "," (plan.activePayloadWords.map toString).toList
  s!"tagged-tuple-return-v1({plan.typeName};active=[{active}])"

def OutputPlan.canonical : OutputPlan → String
  | .dynamic plan => plan.canonical
  | .taggedTuple plan => plan.canonical

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

/-- Canonical identity for every input rule not encoded by the Solidity selector. -/
def AbiInputPlan.inputCanonical (plan : AbiInputPlan) : String :=
  match plan.dynamic with
  | some (.boundedArray array) =>
      s!"bounded-array-v1({plan.typeName};capacity={array.capacity};" ++
        s!"element-words={array.elementWords.size})"
  | some (.packedBytes bytes) =>
      s!"packed-bytes-v1({plan.typeName};capacity={bytes.capacity};" ++
        s!"utf8={bytes.validateUtf8})"
  | none => plan.taggedCanonical

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

/-- EVM keeps the source carrier finite even though standard ABI uses a dynamic tail. This limit
is a target resource bound on generated scalar locals, not an ABI or Core schema limit. -/
def maxBoundedArrayLocalWords : Nat := 64

/-- **ProofForge EVM Bounded Array v1** binds a top-level `BoundedVec α capacity` to canonical
standard ABI `α[]` calldata. Elements must have a static ABI shape. The fixed source frame is
`length:uint32 || capacity × flattened-element`; inactive element locals are zeroed by Emit. -/
def boundedArrayV1InputPlan (capacity : Nat) (element : Schema) : Except String AbiInputPlan := do
  let elementPlan ← staticInputPlan element
  unless !elementPlan.words.isEmpty do
    throw "evm/codec: bounded array element must contain a scalar"
  let localWords := 1 + capacity * elementPlan.wordCount
  unless localWords ≤ maxBoundedArrayLocalWords do
    throw s!"evm/codec: bounded array local frame exceeds {maxBoundedArrayLocalWords} words"
  let mut words : Array Scalar := #[.uint32]
  let mut projections : Array AbiProjection := #[{
    sourceName := "length"
    wordIndex := 0
    partCount := 1
  }]
  for i in [0:capacity] do
    words := words ++ elementPlan.words
    let sourcePrefix := "values_" ++ toString i
    for projection in elementPlan.projections do
      projections := projections.push {
        sourceName := if projection.sourceName.isEmpty then sourcePrefix
          else sourcePrefix ++ "_" ++ projection.sourceName
        wordIndex := 1 + i * elementPlan.wordCount + projection.wordIndex
        partCount := projection.partCount
      }
  return {
    typeName := elementPlan.typeName ++ "[]"
    words
    projections
    dynamic := some (.boundedArray { capacity, elementWords := elementPlan.words })
  }

/-- Bind a bounded source byte frame to canonical standard ABI `bytes` or `string`: one dynamic
head offset, a 32-byte length, packed active bytes, and zero right-padding to a word boundary. -/
def packedBytesV1InputPlan (capacity : Nat) (validateUtf8 : Bool) :
    Except String AbiInputPlan := do
  let localWords := 1 + capacity
  unless localWords ≤ maxBoundedArrayLocalWords do
    throw s!"evm/codec: packed bytes local frame exceeds {maxBoundedArrayLocalWords} words"
  let mut projections : Array AbiProjection := #[{
    sourceName := "length"
    wordIndex := 0
    partCount := 1
  }]
  for i in [0:capacity] do
    projections := projections.push {
      sourceName := "values_" ++ toString i
      wordIndex := 1 + i
      partCount := 1
    }
  return {
    typeName := if validateUtf8 then "string" else "bytes"
    words := #[.uint32] ++ Array.replicate capacity .uint8
    projections
    dynamic := some (.packedBytes { capacity, validateUtf8 })
  }

/-- Select an independent top-level dynamic result policy. A bounded result is represented during
source execution as `length || capacity slots`, then encoded as the canonical standard-ABI active
prefix. Nested/tagged dynamics and multi-limb elements remain fail closed. -/
def dynamicOutputPlan (schema : Schema) : Except String (Option DynamicOutputPlan) := do
  let _ ← validate schema
  match schema with
  | .boundedArray capacity element =>
      let elementWords := (← staticAbiLeaves element).map (·.type)
      unless elementWords.size == 1 && limbCount elementWords[0]! == 1 do
        throw "evm/codec: bounded array result currently requires one-limb scalar elements"
      let localWords := 1 + capacity * elementWords.size
      unless localWords ≤ maxBoundedArrayLocalWords do
        throw s!"evm/codec: bounded array result frame exceeds {maxBoundedArrayLocalWords} words"
      return some (.boundedArray {
        capacity, elementTypeName := ← abiTypeOfSchema element, elementWords
      })
  | .boundedBytes capacity =>
      unless 1 + capacity ≤ maxBoundedArrayLocalWords do
        throw s!"evm/codec: packed bytes result frame exceeds {maxBoundedArrayLocalWords} words"
      return some (.packedBytes { capacity, validateUtf8 := false })
  | .boundedString capacity =>
      unless 1 + capacity ≤ maxBoundedArrayLocalWords do
        throw s!"evm/codec: packed bytes result frame exceeds {maxBoundedArrayLocalWords} words"
      return some (.packedBytes { capacity, validateUtf8 := true })
  | _ => pure none

private def enumPayloadWords : Schema → Except String Nat
  | .unit => pure 0
  | .scalar (.uint 64) => pure 1
  | .tuple items => do
      unless items.all (· == .scalar .uint64) do
        throw "evm/codec: tagged tuple v1 enum fields must be UInt64"
      return items.size
  | _ => throw "evm/codec: tagged tuple v1 enum fields must be UInt64"

/-- Derive Tagged Tuple v1 returndata geometry independently from the input plan. The first slice
matches Extract's fixed tagged-result frame: one-limb scalar Option payloads and unit/UInt64 enum
payloads. Constructed, richer, and nested tagged results remain fail closed. -/
def taggedTupleV1OutputPlan : Schema → Except String TaggedTupleOutputPlan
  | .option (.scalar type) => do
      unless Scalar.isWellFormed type && limbCount type == 1 do
        throw "evm/codec: tagged tuple v1 Option result requires a one-limb scalar payload"
      pure {
        typeName := "(bool," ++ (← abiType type) ++ ")"
        words := #[.boolean, type]
        activePayloadWords := #[0, 1]
      }
  | .option _ =>
      throw "evm/codec: tagged tuple v1 Option result requires a one-limb scalar payload"
  | .enumeration _ tagBits variants => do
      unless tagBits == 8 && !variants.isEmpty && variants.size ≤ 256 do
        throw "evm/codec: tagged tuple v1 enum result requires a nonempty uint8 tag space"
      let counts ← variants.mapM fun variant => enumPayloadWords variant.2
      let payloadWords := counts.foldl (init := 0) max
      unless 1 + payloadWords ≤ maxBoundedArrayLocalWords do
        throw s!"evm/codec: tagged tuple result frame exceeds {maxBoundedArrayLocalWords} words"
      let types := #["uint8"] ++ Array.replicate payloadWords "uint64"
      pure {
        typeName := "(" ++ String.intercalate "," types.toList ++ ")"
        words := #[.uint8] ++ Array.replicate payloadWords .uint64
        activePayloadWords := counts
      }
  | _ => throw "evm/codec: tagged tuple v1 output requires Option or enum"

/-- Select exactly one target-owned ABI output policy. Static scalars/aggregates return `none` and
continue through their existing fixed-word encoder. -/
def outputPlan (schema : Schema) : Except String (Option OutputPlan) := do
  if let some plan ← dynamicOutputPlan schema then
    return some (.dynamic plan)
  match schema with
  | .option _ | .enumeration .. => return some (.taggedTuple (← taggedTupleV1OutputPlan schema))
  | _ => pure none

/-- **ProofForge EVM Tagged Tuple v1** is the explicit standard-ABI input policy for logical sums.

* `Option<T>` is `(bool present,T value)`. An absent value requires every payload word to be zero.
* A payload enum is `(uint8 tag,uint64 p0,...)`, with enough lanes for its largest constructor.
  The tag is the source constructor ordinal and every lane inactive for that constructor is zero.

The fixed tuple avoids dynamic offsets and gives every source projection one bounded ABI word.
Its input plan remains independent from the output plan selected above. -/
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
  | .boundedArray capacity element => boundedArrayV1InputPlan capacity element
  | .boundedBytes capacity => packedBytesV1InputPlan capacity false
  | .boundedString capacity => packedBytesV1InputPlan capacity true
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
