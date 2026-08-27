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
  /-- Width of each Borsh `Option<T>` payload at the end of the wire plan. The corresponding method
  parameters are `(u8 presence, T value)` pairs after the fixed prefix. -/
  optionWidths : Array Nat := #[]
  /-- Exact packed widths for scalar return leaves. Empty means the normal consecutive-u64 ABI. -/
  returnWidths : Array Nat := #[]
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

def RawEntry.minDataLen (entry : RawEntry) : Nat :=
  let fixedWidths := entry.paramWidths.extract 0 entry.fixedParamCount
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
    if entry.optionWidths.isEmpty then base
    else
      let options := String.intercalate "," (entry.optionWidths.map toString).toList
      s!"{base}.borsh-options.[{options}]"
  if entry.returnWidths.isEmpty then base
  else
    let returns := String.intercalate "," (entry.returnWidths.map toString).toList
    s!"{base}.returns.[{returns}]"

def RawEntry.returnDataLen (entry : RawEntry) : Nat :=
  entry.returnWidths.foldl (init := 0) (· + ·)

/-- A final narrow scalar still uses one full eight-byte temporary store. The padding is outside
the bytes passed to `sol_set_return_data`, but remains part of the fixed scratch proof. -/
def RawEntry.returnScratchBytes (entry : RawEntry) : Nat :=
  match entry.returnWidths.back? with
  | none => 0
  | some width => entry.returnDataLen + (8 - width)

private def supportedWidth (width : Nat) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

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
    (paramWidths : Array Nat) (retCount : Nat) : Except String RawEntry := do
  let parts := annotation.splitOn ":"
  unless paramWidths.size == paramCount do
    throw "extract/unsupported: svm raw entry parameter widths are incomplete"
  unless paramWidths.all supportedWidth do
    throw "extract/unsupported: svm raw entry only supports u8/u16/u32/u64 parameters"
  let (tag, accountCount, programAccount) ←
    if parts.length ≥ 4 then parseHeader parts
    else throw "extract/unsupported: malformed svm raw entry annotation"
  let (variant, optionWidths, returnWidths) ←
    if parts.length == 4 && parts[0]! == "svm.raw.v1" then
      pure (none, #[], #[])
    else if parts.length == 6 && parts[0]! == "svm.raw.v2" then do
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
      pure (none, widths, #[])
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
      pure (none, #[], widths)
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
      pure (some variant, #[], widths)
    else
      throw "extract/unsupported: malformed svm raw entry annotation"
  let entry := { tag, accountCount, programAccount, variant, paramWidths, optionWidths, returnWidths }
  unless entry.maxDataLen ≤ 1024 do
    throw "extract/unsupported: svm raw entry data exceeds 1024 bytes"
  unless entry.returnScratchBytes ≤ 304 do
    throw "extract/unsupported: svm raw packed return exceeds scalar scratch"
  return entry

/-- Decode the target annotation once at SVM projection. It never becomes a value or effect Op. -/
def decode (annotations : Array String) (paramCount : Nat)
    (paramWidths : Array Nat) (retCount : Nat := 1) : Except String MethodEntry := do
  let raw := annotations.filter (·.startsWith "svm.raw.")
  if raw.isEmpty then
    return .generated
  unless raw.size == 1 do
    throw "extract/unsupported: method has multiple svm raw entry annotations"
  return .raw (← decodeRaw raw[0]! paramCount paramWidths retCount)

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
