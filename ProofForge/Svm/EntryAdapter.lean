namespace ProofForge.Svm.EntryAdapter

/-- A packed Solana instruction selected by one leading u8. Parameters are widened to the normal
ProofForge scalar representation before the method CFG runs. Account indexes are physical outer
instruction indexes, unlike CPI metas, which remain relative to the external-account region. -/
structure RawEntry where
  tag : Nat
  accountCount : Nat
  programAccount : Nat
  paramWidths : Array Nat
  deriving BEq, Repr, Inhabited

inductive MethodEntry where
  | generated
  | raw (entry : RawEntry)
  deriving BEq, Repr, Inhabited

def MethodEntry.isGenerated : MethodEntry → Bool
  | .generated => true
  | .raw _ => false

def RawEntry.dataLen (entry : RawEntry) : Nat :=
  1 + entry.paramWidths.foldl (init := 0) (· + ·)

def RawEntry.canonical (entry : RawEntry) : String :=
  let widths := String.intercalate "," (entry.paramWidths.map toString).toList
  s!"raw.u8.{entry.tag}.a{entry.accountCount}.p{entry.programAccount}.[{widths}]"

private def decodeRaw (annotation : String) (paramCount : Nat)
    (paramWidths : Array Nat) : Except String RawEntry := do
  let parts := annotation.splitOn ":"
  unless parts.length == 4 && parts[0]! == "svm.raw.v1" do
    throw "extract/unsupported: malformed svm raw entry annotation"
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
  unless paramWidths.size == paramCount do
    throw "extract/unsupported: svm raw entry parameter widths are incomplete"
  unless paramWidths.all fun width => width == 1 || width == 2 || width == 4 || width == 8 do
    throw "extract/unsupported: svm raw entry only supports u8/u16/u32/u64 parameters"
  let entry := { tag, accountCount, programAccount, paramWidths }
  unless entry.dataLen ≤ 1024 do
    throw "extract/unsupported: svm raw entry data exceeds 1024 bytes"
  return entry

/-- Decode the target annotation once at SVM projection. It never becomes a value or effect Op. -/
def decode (annotations : Array String) (paramCount : Nat)
    (paramWidths : Array Nat) : Except String MethodEntry := do
  let raw := annotations.filter (·.startsWith "svm.raw.")
  if raw.isEmpty then
    return .generated
  unless raw.size == 1 do
    throw "extract/unsupported: method has multiple svm raw entry annotations"
  return .raw (← decodeRaw raw[0]! paramCount paramWidths)

def validateUniqueTags (entries : Array MethodEntry) : Except String Unit := do
  let mut seen : Array Nat := #[]
  for entry in entries do
    match entry with
    | .generated => pure ()
    | .raw raw =>
        if seen.contains raw.tag then
          throw s!"extract/unsupported: duplicate svm raw entry tag {raw.tag}"
        seen := seen.push raw.tag

end ProofForge.Svm.EntryAdapter
