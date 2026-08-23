import ProofForge.Extract.LegacyIR
import ProofForge.Crypto.Sha256

namespace ProofForge.Svm.ABI

open ProofForge.Crypto

/-- Agave's currently enforced transaction account-lock limit. -/
def maxTxAccountLocks : Nat := 64

/-- One slot is reserved from the 256 transaction-account entries for `NON_DUP_MARKER`. -/
def maxAccountsPerInstruction : Nat := 255

def accInRange (acc : Nat) : Bool :=
  acc < maxTxAccountLocks

def ixParamSig (paramCount : Nat) : String :=
  String.intercalate "," (List.replicate paramCount "u64")

/-- `sha256("proof-forge-solana-v1:" ++ name ++ "(" ++ sig ++ ")")` input. -/
def discPreimage (ixName : String) (paramCount : Nat) : String :=
  s!"proof-forge-solana-v1:{ixName}({ixParamSig paramCount})"

def discHexOf (ixName : String) (paramCount : Nat) : Except String String :=
  .ok s!"0x{Core.IR.u64Hex (Sha256.first8Le (discPreimage ixName paramCount))}"

def discHex (method : Extract.Legacy.Method) : Except String String :=
  discHexOf method.ixName method.paramCount

private def sourceSlots (program : Extract.Legacy.Program) : Array Core.IR.Slot :=
  program.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

/-- Physical SVM field offset for target-neutral source slots. -/
def fieldOffsetOf (slots : Array Core.IR.Slot) (name : String) : Option Nat :=
  Id.run do
    let mut offset : Nat := 8
    for slot in slots do
      if slot.name == name then return some offset
      offset := offset + slot.width
    return none

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def fieldOffset (program : Extract.Legacy.Program) (name : String) : Option Nat :=
  fieldOffsetOf (sourceSlots program) name

structure VectorStorage where
  baseSlot : Nat
  length : Nat
  strideBytes : Nat
  strideSlots : Nat
  deriving BEq, Repr, Inhabited

private def legacyVectorStorage (program : Extract.Legacy.Program) (name : String) :
    Option VectorStorage :=
  let prefix0 := name ++ "_0"
  let group :=
    program.slots.filter fun slot =>
      slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
  if group.isEmpty then none
  else
    let width := group.foldl (init := 0) fun acc slot => acc + slot.width
    let digitPrefix (value : String) : String := Id.run do
      let mut out := ""
      for char in value.toList do
        if char.isDigit then out := out.push char else return out
      return out
    let length := program.slots.foldl (init := 0) fun acc slot =>
      let rest :=
        if slot.name.startsWith (name ++ "_") then
          digitPrefix (slot.name.drop (name.length + 1) |>.copy)
        else ""
      match rest.toNat? with
      | some index => Nat.max acc (index + 1)
      | none => acc
    let baseSlot := program.slots.findIdx fun slot =>
      slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
    if length == 0 || width == 0 then none
    else some { baseSlot, length, strideBytes := width, strideSlots := group.size }

def vectorStorage (program : Extract.Legacy.Program) (name : String) : Option VectorStorage :=
  match program.schema.vector? name with
  | some vector => do
      let baseSlot ← program.schema.vectorBaseLeafIndex? vector
      return {
        baseSlot
        length := vector.length
        strideBytes := vector.elementBytes
        strideSlots := vector.elementLeaves
      }
  | none => legacyVectorStorage program name

def vectorElem (program : Extract.Legacy.Program) (name : String) : Option (Nat × Nat) :=
  (vectorStorage program name).map fun layout => (layout.length, layout.strideBytes)

def vectorLenOf (program : Extract.Legacy.Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given
  else (vectorElem program name).map (·.1) |>.getD 0

def vectorStride (program : Extract.Legacy.Program) (name : String) : Nat :=
  (vectorElem program name).map (·.2) |>.getD 8

private def slotOffsetAt (program : Extract.Legacy.Program) (index : Nat) : Option Nat :=
  if index >= program.slots.size then none
  else
    let before := program.slots.extract 0 index
    some (8 + before.foldl (init := 0) fun acc slot => acc + slot.width)

def vectorBaseOffset (program : Extract.Legacy.Program) (name : String) : Option Nat := do
  let layout ← vectorStorage program name
  slotOffsetAt program layout.baseSlot

def vectorBaseSlot (program : Extract.Legacy.Program) (name : String) : Option Nat :=
  (vectorStorage program name).map (·.baseSlot)

private def legacyVectorLeafOff (program : Extract.Legacy.Program) (name leaf : String) : Nat :=
  let prefix0 := name ++ "_0"
  Id.run do
    let mut offset : Nat := 0
    for slot in program.slots do
      if slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_") then
        if slot.name == prefix0 ++ "_" ++ leaf || (leaf.isEmpty && slot.name == prefix0) then
          return offset
        offset := offset + slot.width
    return offset

def vectorLeafOff (program : Extract.Legacy.Program) (name leaf : String) : Nat :=
  match program.schema.vector? name with
  | some vector => Id.run do
      let mut offset : Nat := 0
      for item in program.schema.vectorElementLeaves vector do
        if vector.relativeLeafName item == leaf then return offset
        offset := offset + item.width
      return offset
  | none => legacyVectorLeafOff program name leaf

private def legacyVectorLeafName (program : Extract.Legacy.Program) (name : String)
    (offset : Nat) : String :=
  let prefix0 := name ++ "_0"
  Id.run do
    let mut current : Nat := 0
    for slot in program.slots do
      if slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_") then
        if current == offset then
          let suffix := prefix0 ++ "_"
          if slot.name.startsWith suffix then
            return (slot.name.drop suffix.length |>.copy)
          return ""
        current := current + slot.width
    return "value"

def vectorLeafName (program : Extract.Legacy.Program) (name : String) (offset : Nat) : String :=
  match program.schema.vector? name with
  | some vector => Id.run do
      let mut current : Nat := 0
      for item in program.schema.vectorElementLeaves vector do
        if current == offset then return vector.relativeLeafName item
        current := current + item.width
      return "value"
  | none => legacyVectorLeafName program name offset

def dataLenOf (slots : Array Core.IR.Slot) : Nat :=
  let raw := 8 + slots.foldl (init := 0) fun acc slot => acc + slot.width
  raw + (8 - raw % 8) % 8

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def dataLen (program : Extract.Legacy.Program) : Nat :=
  dataLenOf (sourceSlots program)

/-- Loader V3 single-account data begins at `0x60`. -/
def acc0Data : Nat := 0x60
def maxPermittedDataIncrease : Nat := 10240

structure InputLayout where
  rentEpoch : Nat
  instructionDataLen : Nat
  instructionData : Nat
  deriving BEq, Repr, Inhabited

def accountPrefix : Nat := 0x58

def accountSpan (accountDataLen : Nat) : Nat :=
  let dataEnd := accountPrefix + accountDataLen + maxPermittedDataIncrease
  dataEnd + (8 - dataEnd % 8) % 8 + 8

def usesCpi (program : Extract.Legacy.Program) : Bool :=
  program.methods.any fun method => Ops.hasInvoke method.ops

def usesWalk (program : Extract.Legacy.Program) : Bool :=
  usesCpi program || program.methods.any fun method => Ops.hasAcc1 method.ops

def usesSystemTransfer (program : Extract.Legacy.Program) : Bool :=
  usesCpi program

def cpiAccountCount (program : Extract.Legacy.Program) : Nat :=
  let rec maxIndex (fuel : Nat) (ops : Array Ops.Op) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
        ops.foldl (init := acc) fun current op =>
          match op with
          | .invoke programIndex metas .. =>
              let metaIndex := metas.foldl (init := programIndex) fun result item =>
                Nat.max result item.acc
              Nat.max current metaIndex
          | .ite _ _ _ thenOps elseOps =>
              Nat.max (maxIndex fuel' thenOps current) (maxIndex fuel' elseOps current)
          | .forBody _ body => maxIndex fuel' body current
          | _ => current
  let highest := program.methods.foldl (init := 0) fun acc method =>
    Nat.max acc (maxIndex 8 method.ops 0)
  let fromInvoke := if usesCpi program then Nat.max 2 (highest + 1) else 0
  let fromLeaves := program.methods.foldl (init := 0) fun acc method =>
    Nat.max acc (Ops.opsMinAccounts method.ops)
  Nat.max fromInvoke fromLeaves

def inputLayoutOf (accountDataLen : Nat) (walk : Bool) (accountCount : Nat) : InputLayout :=
  if walk then
    let rec lastRent (remaining : Nat) (offset : Nat) : Nat :=
      match remaining with
      | 0 => offset - 8
      | remaining' + 1 => lastRent remaining' (offset + accountSpan 0)
    let rent := lastRent accountCount 8
    { rentEpoch := rent, instructionDataLen := rent + 8, instructionData := rent + 16 }
  else
    let dataEnd := acc0Data + accountDataLen + maxPermittedDataIncrease
    let rent := dataEnd + (8 - dataEnd % 8) % 8
    { rentEpoch := rent, instructionDataLen := rent + 8, instructionData := rent + 16 }

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def inputLayout (program : Extract.Legacy.Program) : InputLayout :=
  inputLayoutOf (dataLen program) (usesWalk program) (cpiAccountCount program)

def layoutSlotName (name : String) : String :=
  if name == "value" then "count" else name

def layoutSigOf (slots : Array Core.IR.Slot) : String :=
  let parts := Id.run do
    let mut result : Array String := #[]
    let mut index : Nat := 0
    let mut offset : Nat := 8
    for slot in slots do
      result := result.push
        s!"{index}:{layoutSlotName slot.name}:0:{offset}:{slot.width}:{slot.abi}"
      offset := offset + slot.width
      index := index + 1
    return result
  s!"{slots.size}|{String.intercalate "|" parts.toList}"

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def layoutSig (program : Extract.Legacy.Program) : String :=
  layoutSigOf (sourceSlots program)

def layoutPreimageOf (slots : Array Core.IR.Slot) : String :=
  s!"proof-forge-solana-layout-v1:{layoutSigOf slots}"

def layoutPreimage (program : Extract.Legacy.Program) : String :=
  layoutPreimageOf (sourceSlots program)

def layoutMarkerHexOf (slots : Array Core.IR.Slot) : Except String String :=
  .ok s!"0x{Core.IR.u64Hex (Sha256.first8Be (layoutPreimageOf slots))}"

def layoutMarkerHex (program : Extract.Legacy.Program) : Except String String :=
  layoutMarkerHexOf (sourceSlots program)

end ProofForge.Svm.ABI
