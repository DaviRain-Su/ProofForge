import ProofForge.Core.Codec

namespace ProofForge.Svm.EntryAdapter

/-- One target-owned Borsh decoder tree. Local indexes refer to fixed scalar scratch slots, never
to account offsets or native pointers. Tagged nodes make branch-dependent wire geometry explicit
without adding a source Op or a main-emitter case. -/
inductive BorshDecode where
  | sequence (items : Array BorshDecode)
  | scalar (localIndex : Nat) (width : Nat) (canonicalBool : Bool)
  | option (tagLocal : Nat) (payloadLocals : Array Nat) (payload : BorshDecode)
  | enumeration (tagLocal : Nat) (payloadLocals : Array Nat)
      (variants : Array BorshDecode)
  | boundedArray (lengthLocal : Nat) (elementLocals : Array Nat)
      (elements : Array BorshDecode)
  | boundedBytes (lengthLocal : Nat) (byteLocals : Array Nat) (validateUtf8 : Bool)
  deriving BEq, Repr, Inhabited

/-- A source projection into one fixed scalar range of a Borsh parameter. Empty `sourceName`
denotes the parameter itself; all other names match Extract's flattened compatibility spelling. -/
structure BorshProjection where
  sourceName : String
  localStart : Nat
  partCount : Nat
  deriving BEq, Repr, Inhabited

/-- Complete target-owned plan for one logical parameter. `localWidths` describes the fixed
invocation-local representation; min/max describe only its conditional Borsh wire bytes. -/
structure BorshPlan where
  decode : BorshDecode
  projections : Array BorshProjection
  localWidths : Array Nat
  localBooleans : Array Bool
  minBytes : Nat
  maxBytes : Nat
  deriving BEq, Repr, Inhabited

def BorshPlan.localCount (plan : BorshPlan) : Nat := plan.localWidths.size

/-- Target-owned conditional Borsh return geometry. Source results are always a fixed scalar
frame; runtime length or tag selects the active wire prefix. Keeping this separate from
`BorshDecode` prevents input cursor rules from becoming an accidental output contract. -/
inductive BorshReturnPlan where
  | boundedArray (capacity : Nat) (elementWidths : Array Nat)
  | packedBytes (capacity : Nat) (validateUtf8 : Bool)
  | option (payloadWidths : Array Nat)
  | enumeration (activePayloadWords : Array Nat)
  deriving BEq, Repr, Inhabited

def BorshReturnPlan.sourceValueCount (plan : BorshReturnPlan) : Nat :=
  match plan with
  | .boundedArray capacity widths => 1 + capacity * widths.size
  | .packedBytes capacity _ => 1 + capacity
  | .option widths => 1 + widths.size
  | .enumeration counts => 1 + counts.foldl (init := 0) max

def BorshReturnPlan.maxBytes (plan : BorshReturnPlan) : Nat :=
  match plan with
  | .boundedArray capacity widths => 4 + capacity * widths.foldl (init := 0) (· + ·)
  | .packedBytes capacity _ => 4 + capacity
  | .option widths => 1 + widths.foldl (init := 0) (· + ·)
  | .enumeration counts => 1 + 8 * counts.foldl (init := 0) max

private def BorshReturnPlan.canonical : BorshReturnPlan → String
  | .boundedArray capacity widths =>
      s!"array.{capacity}.[{String.intercalate "," (widths.map toString).toList}]"
  | .packedBytes capacity validateUtf8 =>
      s!"{if validateUtf8 then "string" else "bytes"}.{capacity}"
  | .option widths =>
      s!"option.[{String.intercalate "," (widths.map toString).toList}]"
  | .enumeration counts =>
      s!"enum.[{String.intercalate "," (counts.map toString).toList}]"

private partial def BorshDecode.canonical : BorshDecode → String
  | .sequence items =>
      s!"s[{String.intercalate "," (items.map BorshDecode.canonical).toList}]"
  | .scalar localIndex width canonicalBool =>
      s!"v{localIndex}.{width}.{if canonicalBool then 1 else 0}"
  | .option tagLocal payloadLocals payload =>
      let locals := String.intercalate "," (payloadLocals.map toString).toList
      s!"o{tagLocal}.[{locals}]({payload.canonical})"
  | .enumeration tagLocal payloadLocals variants =>
      let locals := String.intercalate "," (payloadLocals.map toString).toList
      let bodies := String.intercalate "," (variants.map BorshDecode.canonical).toList
      s!"e{tagLocal}.[{locals}][{bodies}]"
  | .boundedArray lengthLocal elementLocals elements =>
      let locals := String.intercalate "," (elementLocals.map toString).toList
      let bodies := String.intercalate "," (elements.map BorshDecode.canonical).toList
      s!"a{lengthLocal}.[{locals}][{bodies}]"
  | .boundedBytes lengthLocal byteLocals validateUtf8 =>
      let locals := String.intercalate "," (byteLocals.map toString).toList
      s!"{if validateUtf8 then "t" else "b"}{lengthLocal}.[{locals}]"

/-- A packed Solana instruction selected by one leading u8. Parameters are widened to the normal
ProofForge scalar representation before the method CFG runs. Account indexes are physical outer
instruction indexes, unlike CPI metas, which remain relative to the external-account region. -/
structure RawEntry where
  tag : Nat
  accountCount : Nat
  programAccount : Nat
  /-- Number of source parameters before any aggregate is expanded into fixed scalar locals. Zero
  retains compatibility for manually constructed test descriptors. -/
  paramCount : Nat := 0
  /-- Optional Borsh enum discriminant immediately following `tag`. -/
  variant : Option Nat := none
  paramWidths : Array Nat
  /-- Target-owned Borsh leaf widths after expanding logical multi-limb parameters. Empty retains
  the legacy one-leaf-per-parameter plan for manually constructed fixtures. -/
  paramLeafWidths : Array Nat := #[]
  paramLeafCounts : Array Nat := #[]
  /-- Canonical Borsh Bool guards, one flag per physical scalar local. -/
  paramLeafBooleans : Array Bool := #[]
  /-- Recursive target-owned plans for tagged logical parameters. Empty retains the exact static
  leaf path and the legacy explicit Option adapter. -/
  paramBorshPlans : Array BorshPlan := #[]
  /-- Width of each Borsh `Option<T>` payload at the end of the wire plan. The corresponding method
  parameters are `(u8 presence, T value)` pairs after the fixed prefix. -/
  optionWidths : Array Nat := #[]
  /-- Exact packed widths for scalar return leaves. Empty means the normal consecutive-u64 ABI. -/
  returnWidths : Array Nat := #[]
  /-- Return widths inferred from typed metadata when no explicit packed-return annotation exists. -/
  inferredReturnWidths : Array Nat := #[]
  /-- Dynamic top-level Borsh output plan. It is mutually exclusive with explicit/implicit fixed
  return widths and never owns account or persistent-memory geometry. -/
  returnBorshPlan : Option BorshReturnPlan := none
  /-- The first result leaf is a canonical 0/1 presence flag. Zero leaves return data unset; one
  serializes all later leaves according to `returnWidths`. -/
  optionalReturnData : Bool := false
  deriving BEq, Repr, Inhabited

inductive MethodEntry where
  | generated
  | raw (entry : RawEntry)
  deriving BEq, Repr, Inhabited

def MethodEntry.isGenerated : MethodEntry → Bool
  | .generated => true
  | .raw _ => false

def RawEntry.logicalParamCount (entry : RawEntry) : Nat :=
  if entry.paramCount == 0 then entry.paramWidths.size else entry.paramCount

def RawEntry.fixedParamCount (entry : RawEntry) : Nat :=
  entry.logicalParamCount - 2 * entry.optionWidths.size

def RawEntry.wireParamWidths (entry : RawEntry) : Array Nat :=
  if entry.paramLeafWidths.isEmpty then entry.paramWidths else entry.paramLeafWidths

def RawEntry.wireReturnWidths (entry : RawEntry) : Array Nat :=
  if entry.returnWidths.isEmpty then entry.inferredReturnWidths else entry.returnWidths

def RawEntry.paramLeafStart (entry : RawEntry) (index : Nat) : Nat :=
  if entry.paramLeafCounts.isEmpty then index
  else (entry.paramLeafCounts.extract 0 index).foldl (init := 0) (· + ·)

def RawEntry.paramLeafCount (entry : RawEntry) (index : Nat) : Nat :=
  if entry.paramLeafCounts.isEmpty then 1 else (entry.paramLeafCounts[index]?).getD 0

def RawEntry.fixedLeafCount (entry : RawEntry) : Nat :=
  if entry.paramLeafCounts.isEmpty then entry.fixedParamCount
  else (entry.paramLeafCounts.extract 0 entry.fixedParamCount).foldl (init := 0) (· + ·)

def RawEntry.usesSchemaBorsh (entry : RawEntry) : Bool := !entry.paramBorshPlans.isEmpty

def RawEntry.minDataLen (entry : RawEntry) : Nat :=
  let selectorBytes := 1 + if entry.variant.isSome then 1 else 0
  if entry.usesSchemaBorsh then
    selectorBytes + entry.paramBorshPlans.foldl (init := 0) fun size plan =>
      size + plan.minBytes
  else
    let fixedWidths := entry.wireParamWidths.extract 0 entry.fixedLeafCount
    selectorBytes + fixedWidths.foldl (init := 0) (· + ·) + entry.optionWidths.size

def RawEntry.maxDataLen (entry : RawEntry) : Nat :=
  if entry.usesSchemaBorsh then
    1 + (if entry.variant.isSome then 1 else 0) +
      entry.paramBorshPlans.foldl (init := 0) fun size plan => size + plan.maxBytes
  else
    entry.minDataLen + entry.optionWidths.foldl (init := 0) (· + ·)

/-- Compatibility accessor for exact entries; variable entries report their maximum wire length. -/
def RawEntry.dataLen (entry : RawEntry) : Nat := entry.maxDataLen

def RawEntry.isExact (entry : RawEntry) : Bool := entry.minDataLen == entry.maxDataLen

def RawEntry.canonical (entry : RawEntry) : String :=
  let widths := String.intercalate "," (entry.paramWidths.map toString).toList
  let selector := entry.variant.map (s!".variant.{·}") |>.getD ""
  let base :=
    s!"raw.u8.{entry.tag}{selector}.a{entry.accountCount}.p{entry.programAccount}.[{widths}]"
  let base :=
    if entry.paramLeafWidths.isEmpty || entry.paramLeafWidths == entry.paramWidths then base
    else
      let leaves := String.intercalate "," (entry.paramLeafWidths.map toString).toList
      s!"{base}.borsh-leaves.[{leaves}]"
  let base :=
    if entry.paramLeafBooleans.all (· == false) then base
    else
      let guards := String.intercalate "," <| (entry.paramLeafBooleans.mapIdx fun i guard =>
        if guard then some (toString i) else none).filterMap id |>.toList
      s!"{base}.borsh-bool.[{guards}]"
  let base :=
    if entry.usesSchemaBorsh then
      let plans := String.intercalate "," <| entry.paramBorshPlans.map
        (fun plan => s!"{plan.minBytes}-{plan.maxBytes}:{plan.decode.canonical}") |>.toList
      s!"{base}.borsh-schema.[{plans}]"
    else if entry.optionWidths.isEmpty then base
    else
      let options := String.intercalate "," (entry.optionWidths.map toString).toList
      s!"{base}.borsh-options.[{options}]"
  if let some plan := entry.returnBorshPlan then
    s!"{base}.borsh-return-schema.{plan.canonical}"
  else if entry.optionalReturnData then
    let returns := String.intercalate "," (entry.returnWidths.map toString).toList
    s!"{base}.optional-returns.[{returns}]"
  else if entry.returnWidths.isEmpty &&
      (entry.inferredReturnWidths.isEmpty || entry.inferredReturnWidths.all (· == 8)) then base
  else if entry.returnWidths.isEmpty then
    let returns := String.intercalate "," (entry.inferredReturnWidths.map toString).toList
    s!"{base}.borsh-returns.[{returns}]"
  else
    let returns := String.intercalate "," (entry.returnWidths.map toString).toList
    s!"{base}.returns.[{returns}]"

def RawEntry.returnDataLen (entry : RawEntry) : Nat :=
  match entry.returnBorshPlan with
  | some plan => plan.maxBytes
  | none => entry.wireReturnWidths.foldl (init := 0) (· + ·)

/-- Dynamic returns use an exact packed output frame plus one disjoint eight-byte staging slot.
Expression evaluation may use deeper generic scratch, but can no longer overlap published bytes. -/
def RawEntry.returnScratchBytes (entry : RawEntry) : Nat :=
  match entry.returnBorshPlan with
  | some plan => plan.maxBytes + 8
  | none =>
      match entry.wireReturnWidths.back? with
      | none => 0
      | some width => entry.returnDataLen + (8 - width)

private def supportedWidth (width : Nat) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

def scalarLeafWidths (type : Core.Codec.Scalar) : Except String (Array Nat) := do
  unless type.isWellFormed do throw "extract/unsupported: malformed svm boundary scalar"
  match type with
  | .boolean => return #[1]
  | .uint bits =>
      let bytes := bits / 8
      if bytes ≤ 8 then return #[bytes]
      let full := bytes / 8
      let rem := bytes % 8
      return Array.replicate full 8 ++ if rem == 0 then #[] else #[rem]
  | .fixedBytes bytes =>
      let full := bytes / 8
      let rem := bytes % 8
      return Array.replicate full 8 ++ if rem == 0 then #[] else #[rem]
  | .address _ =>
      throw "extract/unsupported: svm raw entry rejects target-specific address values"

structure BorshLeaf where
  logical : Core.Codec.StaticLeaf
  widths : Array Nat
  deriving BEq, Repr, Inhabited

/-- Target-owned fixed Borsh plan. Logical paths come from Core; exact little-endian widths and
Bool canonicality are SVM decisions. No pointer or account offset enters this descriptor. -/
def staticBorshLeaves (schema : Core.Codec.Schema) : Except String (Array BorshLeaf) := do
  let leaves ← Core.Codec.staticLeaves schema
  leaves.mapM fun logical => return { logical, widths := ← scalarLeafWidths logical.type }

private partial def BorshDecode.shift (offset : Nat) : BorshDecode → BorshDecode
  | .sequence items => .sequence (items.map (BorshDecode.shift offset))
  | .scalar localIndex width canonicalBool =>
      .scalar (offset + localIndex) width canonicalBool
  | .option tagLocal payloadLocals payload =>
      .option (offset + tagLocal) (payloadLocals.map (offset + ·)) (payload.shift offset)
  | .enumeration tagLocal payloadLocals variants =>
      .enumeration (offset + tagLocal) (payloadLocals.map (offset + ·))
        (variants.map (BorshDecode.shift offset))
  | .boundedArray lengthLocal elementLocals elements =>
      .boundedArray (offset + lengthLocal) (elementLocals.map (offset + ·))
        (elements.map (BorshDecode.shift offset))
  | .boundedBytes lengthLocal byteLocals validateUtf8 =>
      .boundedBytes (offset + lengthLocal) (byteLocals.map (offset + ·)) validateUtf8

private def BorshProjection.shift (projection : BorshProjection) (offset : Nat) :
    BorshProjection :=
  { projection with localStart := offset + projection.localStart }

private def BorshPlan.shift (plan : BorshPlan) (offset : Nat) : BorshPlan :=
  { plan with
    decode := plan.decode.shift offset
    projections := plan.projections.map (·.shift offset) }

private def sequencePlans (plans : Array BorshPlan) : BorshPlan := Id.run do
  let mut items := #[]
  let mut projections := #[]
  let mut widths := #[]
  let mut booleans := #[]
  let mut minBytes := 0
  let mut maxBytes := 0
  for plan in plans do
    let shifted := plan.shift widths.size
    items := items.push shifted.decode
    projections := projections ++ shifted.projections
    widths := widths ++ plan.localWidths
    booleans := booleans ++ plan.localBooleans
    minBytes := minBytes + plan.minBytes
    maxBytes := maxBytes + plan.maxBytes
  return {
    decode := .sequence items
    projections
    localWidths := widths
    localBooleans := booleans
    minBytes
    maxBytes
  }

private def sourceChild (sourcePrefix child : String) : String :=
  if sourcePrefix.isEmpty then child else sourcePrefix ++ "_" ++ child

private def scalarBorshPlan (sourcePrefix : String) (type : Core.Codec.Scalar) :
    Except String BorshPlan := do
  let widths ← scalarLeafWidths type
  let nodes := widths.mapIdx fun localIndex width =>
    BorshDecode.scalar localIndex width (type == .boolean)
  return {
    decode := .sequence nodes
    projections := #[{ sourceName := sourcePrefix, localStart := 0, partCount := widths.size }]
    localWidths := widths
    localBooleans := Array.replicate widths.size (type == .boolean)
    minBytes := widths.foldl (init := 0) (· + ·)
    maxBytes := widths.foldl (init := 0) (· + ·)
  }

private def localRange (start count : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [0:count] do result := result.push (start + i)
  return result

private def boundedBytePlan (sourcePrefix : String) (capacity : Nat) (validateUtf8 : Bool) :
    BorshPlan := Id.run do
  let lengthName := sourceChild sourcePrefix "length"
  let valuesPrefix := sourceChild sourcePrefix "values"
  let mut projections : Array BorshProjection := #[{
    sourceName := lengthName
    localStart := 0
    partCount := 1
  }]
  for i in [0:capacity] do
    projections := projections.push {
      sourceName := valuesPrefix ++ "_" ++ toString i
      localStart := 1 + i
      partCount := 1
    }
  return {
    decode := .boundedBytes 0 (localRange 1 capacity) validateUtf8
    projections
    localWidths := #[4] ++ Array.replicate capacity 1
    localBooleans := Array.replicate (1 + capacity) false
    minBytes := 4
    maxBytes := 4 + capacity
  }

/-- Extract currently represents payload enums as a tag plus the largest sequence of constructor
`UInt64` fields. Preserve that fixed source representation while allowing each Borsh variant to
have its own exact wire length. Richer enum payloads remain closed until the source representation
can name their fields without ambiguity. -/
private def enumPayloadPlan (base : String) : Core.Codec.Schema → Except String BorshPlan
  | .unit => pure (sequencePlans #[])
  | .scalar (.uint 64) => scalarBorshPlan (base ++ "_p0") .uint64
  | .tuple items => do
      let mut plans := #[]
      for i in [0:items.size] do
        unless items[i]! == .scalar .uint64 do
          throw "extract/unsupported: SVM Borsh enum constructor fields must be UInt64"
        plans := plans.push (← scalarBorshPlan (base ++ "_p" ++ toString i) .uint64)
      return sequencePlans plans
  | _ => throw "extract/unsupported: SVM Borsh enum constructor fields must be UInt64"

private partial def borshPlanAt (sourcePrefix : String) :
    Core.Codec.Schema → Except String BorshPlan
  | .unit => pure (sequencePlans #[])
  | .scalar type => scalarBorshPlan sourcePrefix type
  | .tuple items => do
      let mut plans := #[]
      for i in [0:items.size] do
        let child := match i with
          | 0 => "fst"
          | 1 => "snd"
          | _ => toString i
        plans := plans.push (← borshPlanAt (sourceChild sourcePrefix child) items[i]!)
      return sequencePlans plans
  | .record _ fields => do
      let mut plans := #[]
      for field in fields do
        plans := plans.push (← borshPlanAt (sourceChild sourcePrefix field.1) field.2)
      return sequencePlans plans
  | .fixedArray length element => do
      let mut plans := #[]
      for i in [0:length] do
        plans := plans.push (← borshPlanAt (sourcePrefix ++ "_" ++ toString i) element)
      return sequencePlans plans
  | .option payload => do
      let base := if sourcePrefix.isEmpty then "slot" else sourcePrefix
      let payloadPlan ← borshPlanAt (base ++ "_p0") payload
      let shiftedPayload := payloadPlan.shift 1
      return {
        decode := .option 0 (localRange 1 payloadPlan.localCount) shiftedPayload.decode
        projections := #[{
          sourceName := base ++ "_tag"
          localStart := 0
          partCount := 1
        }] ++ shiftedPayload.projections
        localWidths := #[1] ++ payloadPlan.localWidths
        localBooleans := #[false] ++ payloadPlan.localBooleans
        minBytes := 1
        maxBytes := 1 + payloadPlan.maxBytes
      }
  | .enumeration _ tagBits variants => do
      unless tagBits == 8 do
        throw "extract/unsupported: canonical Borsh enum tags must be u8"
      unless !variants.isEmpty && variants.size ≤ 256 do
        throw "extract/unsupported: canonical Borsh enum variants must fit u8"
      let base := if sourcePrefix.isEmpty then "variant" else sourcePrefix
      let plans ← variants.mapM fun variant => enumPayloadPlan base variant.2
      let maxLocals := plans.foldl (init := 0) fun count plan => max count plan.localCount
      let mut widths := Array.replicate maxLocals 0
      let mut booleans := Array.replicate maxLocals false
      for plan in plans do
        for i in [0:plan.localCount] do
          let width := plan.localWidths[i]!
          if widths[i]! != 0 && widths[i]! != width then
            throw "extract/unsupported: SVM Borsh enum payload slots have incompatible widths"
          widths := widths.set! i width
          booleans := booleans.set! i (booleans[i]! || plan.localBooleans[i]!)
      let minPayload := plans.foldl (init := plans[0]!.minBytes) fun size plan =>
        min size plan.minBytes
      let maxPayload := plans.foldl (init := 0) fun size plan => max size plan.maxBytes
      let mut projections : Array BorshProjection := #[{
        sourceName := base ++ "_tag"
        localStart := 0
        partCount := 1
      }]
      if maxLocals == 0 then
        projections := projections.push {
          sourceName := sourcePrefix
          localStart := 0
          partCount := 1
        }
      else
        for i in [0:maxLocals] do
          projections := projections.push {
            sourceName := base ++ "_p" ++ toString i
            localStart := 1 + i
            partCount := 1
          }
      return {
        decode := .enumeration 0 (localRange 1 maxLocals)
          (plans.map fun plan => (plan.shift 1).decode)
        projections
        localWidths := #[1] ++ widths
        localBooleans := #[false] ++ booleans
        minBytes := 1 + minPayload
        maxBytes := 1 + maxPayload
      }
  | .boundedArray capacity element => do
      let lengthName := sourceChild sourcePrefix "length"
      let valuesPrefix := sourceChild sourcePrefix "values"
      let mut elements := #[]
      let mut projections : Array BorshProjection := #[{
        sourceName := lengthName
        localStart := 0
        partCount := 1
      }]
      let mut widths := #[]
      let mut booleans := #[]
      let mut maxBytes := 4
      for i in [0:capacity] do
        let plan ← borshPlanAt (valuesPrefix ++ "_" ++ toString i) element
        let shifted := plan.shift (1 + widths.size)
        elements := elements.push shifted.decode
        projections := projections ++ shifted.projections
        widths := widths ++ plan.localWidths
        booleans := booleans ++ plan.localBooleans
        maxBytes := maxBytes + plan.maxBytes
      return {
        decode := .boundedArray 0 (localRange 1 widths.size) elements
        projections
        localWidths := #[4] ++ widths
        localBooleans := #[false] ++ booleans
        minBytes := 4
        maxBytes
      }
  | .boundedBytes capacity => pure (boundedBytePlan sourcePrefix capacity false)
  | .boundedString capacity => pure (boundedBytePlan sourcePrefix capacity true)

/-- Derive one recursive SVM-owned Borsh plan from a logical schema. The plan fixes scratch-local
identity and canonical tag handling but carries no account geometry or application policy. -/
def borshPlan (schema : Core.Codec.Schema) : Except String BorshPlan := do
  let _ ← Core.Codec.validate schema
  borshPlanAt "" schema

private def borshReturnPlanAt : Core.Codec.Schema → Except String BorshReturnPlan
  | .boundedArray capacity element => do
      let leaves ← staticBorshLeaves element
      let widths := leaves.foldl (init := #[]) fun out leaf => out ++ leaf.widths
      unless leaves.size == 1 && widths.size == 1 do
        throw "extract/unsupported: bounded Borsh returns currently require one-limb scalar elements"
      pure (.boundedArray capacity widths)
  | .boundedBytes capacity => pure (.packedBytes capacity false)
  | .boundedString capacity => pure (.packedBytes capacity true)
  | .option payload => do
      let leaves ← staticBorshLeaves payload
      let widths := leaves.foldl (init := #[]) fun out leaf => out ++ leaf.widths
      unless leaves.size == 1 && widths.size == 1 do
        throw "extract/unsupported: SVM tagged Option returns require a one-limb scalar payload"
      pure (.option widths)
  | .enumeration _ tagBits variants => do
      unless tagBits == 8 && !variants.isEmpty && variants.size ≤ 256 do
        throw "extract/unsupported: SVM tagged enum returns require a nonempty u8 tag space"
      let counts ← variants.mapM fun variant =>
        match variant.2 with
        | .unit => pure 0
        | .scalar (.uint 64) => pure 1
        | .tuple items => do
            unless items.all (· == .scalar .uint64) do
              throw "extract/unsupported: SVM tagged enum return fields must be UInt64"
            pure items.size
        | _ => throw "extract/unsupported: SVM tagged enum return fields must be UInt64"
      pure (.enumeration counts)
  | _ => throw "extract/unsupported: SVM Borsh return requires a bounded or tagged value"

/-- Derive a top-level conditional Borsh output plan independently from the input decoder. Bounded
elements and tagged payloads must fit the supported fixed scalar frame; nested outputs stay closed. -/
def borshReturnPlan (schema : Core.Codec.Schema) : Except String BorshReturnPlan := do
  let _ ← Core.Codec.validate schema
  borshReturnPlanAt schema

private partial def hasTaggedSchema : Core.Codec.Schema → Bool
  | .option _ | .enumeration .. | .boundedArray .. | .boundedBytes _ | .boundedString _ => true
  | .tuple items => items.any hasTaggedSchema
  | .record _ fields => fields.any (hasTaggedSchema ·.2)
  | .fixedArray _ element => hasTaggedSchema element
  | .unit | .scalar _ => false

private def parseHeader (parts : List String) : Except String (Nat × Nat × Nat) := do
  let some tag := parts[1]!.toNat?
    | throw "extract/unsupported: malformed svm raw entry tag"
  let some accountCount := parts[2]!.toNat?
    | throw "extract/unsupported: malformed svm raw entry account count"
  let some programAccount := parts[3]!.toNat?
    | throw "extract/unsupported: malformed svm raw entry program account"
  unless tag < 256 do
    throw "extract/unsupported: svm raw entry tag must fit u8"
  unless 0 < accountCount && accountCount ≤ 64 && programAccount < accountCount do
    throw "extract/unsupported: svm raw entry account contract is invalid"
  return (tag, accountCount, programAccount)

private def decodeRaw (annotation : String) (paramCount : Nat)
    (paramWidths : Array Nat) (retCount : Nat) (paramTypes retTypes : Array Core.Codec.Scalar)
    (paramSchemas : Array Core.Codec.Schema) (retSchema : Core.Codec.Schema) :
    Except String RawEntry := do
  let parts := annotation.splitOn ":"
  let (paramLeafWidths, paramLeafCounts, paramLeafBooleans, paramBorshPlans) ←
    if !paramSchemas.isEmpty then do
      unless paramSchemas.size == paramCount do
        throw "extract/unsupported: svm raw entry parameter schemas are incomplete"
      if paramSchemas.any hasTaggedSchema then do
        let plans ← paramSchemas.mapM borshPlan
        pure (
          plans.foldl (init := #[]) fun out plan => out ++ plan.localWidths,
          plans.map (·.localCount),
          plans.foldl (init := #[]) fun out plan => out ++ plan.localBooleans,
          plans)
      else do
        let plans ← paramSchemas.mapM staticBorshLeaves
        let widths := plans.map fun plan =>
          plan.foldl (init := #[]) fun out leaf => out ++ leaf.widths
        let booleans := plans.foldl (init := #[]) fun out plan =>
          out ++ plan.foldl (init := #[]) fun flags leaf =>
            flags ++ Array.replicate leaf.widths.size (leaf.logical.type == .boolean)
        pure (widths.foldl (init := #[]) (· ++ ·), widths.map (·.size), booleans, #[])
    else if paramTypes.isEmpty then do
      unless paramWidths.size == paramCount do
        throw "extract/unsupported: svm raw entry parameter widths are incomplete"
      unless paramWidths.all supportedWidth do
        throw "extract/unsupported: svm raw entry has unsupported legacy parameter widths"
      pure (paramWidths, Array.replicate paramCount 1, Array.replicate paramCount false, #[])
    else do
      unless paramWidths.size == paramCount do
        throw "extract/unsupported: svm raw entry parameter widths are incomplete"
      unless paramTypes.size == paramCount do
        throw "extract/unsupported: svm raw entry typed parameter metadata is incomplete"
      let plans ← paramTypes.mapM scalarLeafWidths
      let booleans := (paramTypes.zip plans).foldl (init := #[]) fun out pair =>
        out ++ Array.replicate pair.2.size (pair.1 == .boolean)
      pure (plans.foldl (init := #[]) (· ++ ·), plans.map (·.size), booleans, #[])
  let returnBorshPlan ←
    match retSchema with
    | .option _ | .enumeration .. | .boundedArray .. | .boundedBytes _ | .boundedString _ => do
        let plan ← borshReturnPlan retSchema
        unless plan.sourceValueCount == retCount do
          throw "extract/unsupported: SVM Borsh return metadata is incomplete"
        pure (some plan)
    | _ =>
        if hasTaggedSchema retSchema then
          throw "extract/unsupported: nested SVM Borsh return binding is not implemented"
        else pure none
  let inferredReturnWidths ←
    if returnBorshPlan.isSome then pure #[]
    else if retTypes.isEmpty then
      match staticBorshLeaves retSchema with
      | .ok leaves =>
          let widths := leaves.foldl (init := #[]) fun out leaf => out ++ leaf.widths
          unless retSchema == .unit || widths.size == retCount do
            throw "extract/unsupported: svm raw aggregate return metadata is incomplete"
          pure widths
      | .error _ => pure #[]
    else do
      let plans ← retTypes.mapM scalarLeafWidths
      let widths := plans.foldl (init := #[]) (· ++ ·)
      unless widths.size == retCount do
        throw "extract/unsupported: svm raw entry typed return metadata is incomplete"
      pure widths
  let (tag, accountCount, programAccount) ←
    if parts.length ≥ 4 then parseHeader parts
    else throw "extract/unsupported: malformed svm raw entry annotation"
  let (variant, optionWidths, returnWidths, optionalReturnData) ←
    if parts.length == 4 && parts[0]! == "svm.raw.v1" then
      pure (none, #[], #[], false)
    else if parts.length == 6 && parts[0]! == "svm.raw.v2" then do
      unless paramLeafWidths == paramWidths do
        throw "extract/unsupported: Borsh Option entries currently require one-leaf scalar parameters"
      let some prefixParamCount := parts[4]!.toNat?
        | throw "extract/unsupported: malformed svm raw fixed-prefix count"
      let widthParts := parts[5]!.splitOn ","
      let mut widths := #[]
      for part in widthParts do
        let some width := part.toNat?
          | throw "extract/unsupported: malformed svm raw Borsh option width"
        unless supportedWidth width do
          throw "extract/unsupported: Borsh option payloads must be u8/u16/u32/u64"
        widths := widths.push width
      unless !widths.isEmpty && paramCount == prefixParamCount + 2 * widths.size do
        throw "extract/unsupported: svm raw Borsh option parameter plan is incomplete"
      for i in [0:widths.size] do
        unless paramWidths[prefixParamCount + 2 * i]! == 1 &&
            paramWidths[prefixParamCount + 2 * i + 1]! == widths[i]! do
          throw "extract/unsupported: svm raw Borsh option parameters must be (u8 presence, payload) pairs"
      pure (none, widths, #[], false)
    else if parts.length == 5 && parts[0]! == "svm.raw.v3" then do
      let widthParts := parts[4]!.splitOn ","
      let mut widths := #[]
      for part in widthParts do
        let some width := part.toNat?
          | throw "extract/unsupported: malformed svm raw packed-return width"
        unless supportedWidth width do
          throw "extract/unsupported: packed returns must be u8/u16/u32/u64"
        widths := widths.push width
      unless !widths.isEmpty && widths.size == retCount do
        throw "extract/unsupported: svm raw packed-return plan must cover every result leaf"
      pure (none, #[], widths, false)
    else if parts.length == 6 && parts[0]! == "svm.raw.v4" then do
      let some variant := parts[4]!.toNat?
        | throw "extract/unsupported: malformed Borsh enum variant"
      unless variant < 256 do
        throw "extract/unsupported: Borsh enum variant must fit u8"
      let widthParts := parts[5]!.splitOn ","
      let mut widths := #[]
      for part in widthParts do
        let some width := part.toNat?
          | throw "extract/unsupported: malformed svm raw packed-return width"
        unless supportedWidth width do
          throw "extract/unsupported: packed returns must be u8/u16/u32/u64"
        widths := widths.push width
      unless !widths.isEmpty && widths.size == retCount do
        throw "extract/unsupported: svm raw packed-return plan must cover every result leaf"
      pure (some variant, #[], widths, false)
    else if parts.length == 6 && parts[0]! == "svm.raw.v5" then do
      let some variant := parts[4]!.toNat?
        | throw "extract/unsupported: malformed Borsh enum variant"
      unless variant < 256 do
        throw "extract/unsupported: Borsh enum variant must fit u8"
      let widthParts := parts[5]!.splitOn ","
      let mut widths := #[]
      for part in widthParts do
        let some width := part.toNat?
          | throw "extract/unsupported: malformed optional packed-return width"
        unless supportedWidth width do
          throw "extract/unsupported: optional packed-return width must be 1, 2, 4, or 8"
        widths := widths.push width
      unless !widths.isEmpty && widths.size + 1 == retCount do
        throw "extract/unsupported: optional packed-return plan must cover every payload result leaf"
      pure (some variant, #[], widths, true)
    else
      throw "extract/unsupported: malformed svm raw entry annotation"
  if returnBorshPlan.isSome && (!returnWidths.isEmpty || optionalReturnData) then
    throw "extract/unsupported: dynamic Borsh returns cannot use an explicit return annotation"
  let entry := {
    tag, accountCount, programAccount, paramCount, variant, paramWidths, paramLeafWidths,
    paramLeafCounts, paramLeafBooleans, paramBorshPlans, optionWidths, returnWidths,
    inferredReturnWidths, returnBorshPlan, optionalReturnData
  }
  unless entry.maxDataLen ≤ 1024 do
    throw "extract/unsupported: svm raw entry data exceeds 1024 bytes"
  unless entry.returnScratchBytes ≤ 304 do
    throw "extract/unsupported: svm raw packed return exceeds scalar scratch"
  return entry

/-- Decode the target annotation once at SVM projection. It never becomes a value or effect Op. -/
def decode (annotations : Array String) (paramCount : Nat)
    (paramWidths : Array Nat) (retCount : Nat := 1)
    (paramTypes : Array Core.Codec.Scalar := #[])
    (retTypes : Array Core.Codec.Scalar := #[])
    (paramSchemas : Array Core.Codec.Schema := #[])
    (retSchema : Core.Codec.Schema := .unit) : Except String MethodEntry := do
  let raw := annotations.filter (·.startsWith "svm.raw.")
  if raw.isEmpty then
    return .generated
  unless raw.size == 1 do
    throw "extract/unsupported: method has multiple svm raw entry annotations"
  return .raw (← decodeRaw raw[0]! paramCount paramWidths retCount paramTypes retTypes
    paramSchemas retSchema)

def validateUniqueTags (entries : Array MethodEntry) : Except String Unit := do
  let mut seen : Array (Nat × Option Nat) := #[]
  for entry in entries do
    match entry with
    | .generated => pure ()
    | .raw raw =>
        if seen.any fun (tag, variant) =>
            tag == raw.tag && (variant.isNone || raw.variant.isNone || variant == raw.variant) then
          throw s!"extract/unsupported: duplicate svm raw entry selector {raw.tag}/{raw.variant}"
        seen := seen.push (raw.tag, raw.variant)

end ProofForge.Svm.EntryAdapter
