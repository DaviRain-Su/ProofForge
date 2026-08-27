import ProofForge.Core.Codec

namespace ProofForge.Svm.EntryAdapter

/-- A packed Solana instruction selected by one leading u8. Parameters are widened to the normal
ProofForge scalar representation before the method CFG runs. Account indexes are physical outer
instruction indexes, unlike CPI metas, which remain relative to the external-account region. -/
structure RawEntry where
  tag : Nat
  accountCount : Nat
  programAccount : Nat
  /-- Optional Borsh enum discriminant immediately following `tag`. -/
  variant : Option Nat := none
  paramWidths : Array Nat
  /-- Target-owned Borsh leaf widths after expanding logical multi-limb parameters. Empty retains
  the legacy one-leaf-per-parameter plan for manually constructed fixtures. -/
  paramLeafWidths : Array Nat := #[]
  paramLeafCounts : Array Nat := #[]
  /-- Width of each Borsh `Option<T>` payload at the end of the wire plan. The corresponding method
  parameters are `(u8 presence, T value)` pairs after the fixed prefix. -/
  optionWidths : Array Nat := #[]
  /-- Exact packed widths for scalar return leaves. Empty means the normal consecutive-u64 ABI. -/
  returnWidths : Array Nat := #[]
  /-- Return widths inferred from typed metadata when no explicit packed-return annotation exists. -/
  inferredReturnWidths : Array Nat := #[]
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

def RawEntry.fixedParamCount (entry : RawEntry) : Nat :=
  entry.paramWidths.size - 2 * entry.optionWidths.size

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

def RawEntry.minDataLen (entry : RawEntry) : Nat :=
  let fixedWidths := entry.wireParamWidths.extract 0 entry.fixedLeafCount
  1 + (if entry.variant.isSome then 1 else 0) +
    fixedWidths.foldl (init := 0) (· + ·) + entry.optionWidths.size

def RawEntry.maxDataLen (entry : RawEntry) : Nat :=
  entry.minDataLen + entry.optionWidths.foldl (init := 0) (· + ·)

/-- Compatibility accessor for exact entries; variable entries report their maximum wire length. -/
def RawEntry.dataLen (entry : RawEntry) : Nat := entry.maxDataLen

def RawEntry.isExact (entry : RawEntry) : Bool := entry.optionWidths.isEmpty

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
    if entry.optionWidths.isEmpty then base
    else
      let options := String.intercalate "," (entry.optionWidths.map toString).toList
      s!"{base}.borsh-options.[{options}]"
  if entry.optionalReturnData then
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
  entry.wireReturnWidths.foldl (init := 0) (· + ·)

/-- A final narrow scalar still uses one full eight-byte temporary store. The padding is outside
the bytes passed to `sol_set_return_data`, but remains part of the fixed scratch proof. -/
def RawEntry.returnScratchBytes (entry : RawEntry) : Nat :=
  match entry.wireReturnWidths.back? with
  | none => 0
  | some width => entry.returnDataLen + (8 - width)

private def supportedWidth (width : Nat) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

private def leafWidths (type : Core.Codec.Scalar) : Except String (Array Nat) := do
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
    (paramWidths : Array Nat) (retCount : Nat) (paramTypes retTypes : Array Core.Codec.Scalar) :
    Except String RawEntry := do
  let parts := annotation.splitOn ":"
  unless paramWidths.size == paramCount do
    throw "extract/unsupported: svm raw entry parameter widths are incomplete"
  let (paramLeafWidths, paramLeafCounts) ←
    if paramTypes.isEmpty then do
      unless paramWidths.all supportedWidth do
        throw "extract/unsupported: svm raw entry has unsupported legacy parameter widths"
      pure (paramWidths, Array.replicate paramCount 1)
    else do
      unless paramTypes.size == paramCount do
        throw "extract/unsupported: svm raw entry typed parameter metadata is incomplete"
      let plans ← paramTypes.mapM leafWidths
      pure (plans.foldl (init := #[]) (· ++ ·), plans.map (·.size))
  let inferredReturnWidths ←
    if retTypes.isEmpty then pure #[]
    else do
      let plans ← retTypes.mapM leafWidths
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
  let entry := {
    tag, accountCount, programAccount, variant, paramWidths, paramLeafWidths, paramLeafCounts,
    optionWidths, returnWidths, inferredReturnWidths, optionalReturnData
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
    (retTypes : Array Core.Codec.Scalar := #[]) : Except String MethodEntry := do
  let raw := annotations.filter (·.startsWith "svm.raw.")
  if raw.isEmpty then
    return .generated
  unless raw.size == 1 do
    throw "extract/unsupported: method has multiple svm raw entry annotations"
  return .raw (← decodeRaw raw[0]! paramCount paramWidths retCount paramTypes retTypes)

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
