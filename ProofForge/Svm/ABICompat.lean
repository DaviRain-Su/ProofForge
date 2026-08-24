import ProofForge.Svm.ABI
import ProofForge.Extract.LegacyIR

namespace ProofForge.Svm.ABI

def discHex (method : Extract.Legacy.Method) : Except String String :=
  discHexOf method.ixName method.paramCount

private def sourceSlots (program : Extract.Legacy.Program) : Array Core.IR.Slot :=
  program.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

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

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def dataLen (program : Extract.Legacy.Program) : Nat :=
  dataLenOf (sourceSlots program)

def usesCpi (program : Extract.Legacy.Program) : Bool :=
  program.methods.any fun method => ProofForge.Ops.hasInvoke method.ops

def usesWalk (program : Extract.Legacy.Program) : Bool :=
  usesCpi program || program.methods.any fun method => ProofForge.Ops.hasAcc1 method.ops

def usesSystemTransfer (program : Extract.Legacy.Program) : Bool :=
  usesCpi program

private partial def highestInvokeIndex (ops : Array ProofForge.Ops.Op) : Nat :=
  ops.foldl (init := 0) fun result op =>
    match op with
    | .invoke programIndex metas data .. =>
      let fromMetas := metas.foldl (init := Nat.max result programIndex) fun value entry =>
          Nat.max value entry.acc
      data.foldl (init := fromMetas) fun value word =>
        match word with
        | .accKey accountIndex => Nat.max value accountIndex
        | _ => value
    | .ite _ _ _ thn els =>
        Nat.max result (Nat.max (highestInvokeIndex thn) (highestInvokeIndex els))
    | .forBody _ body => Nat.max result (highestInvokeIndex body)
    | _ => result

def cpiAccountCount (program : Extract.Legacy.Program) : Nat :=
  let highest := program.methods.foldl (init := 0) fun acc method =>
    Nat.max acc (highestInvokeIndex method.ops)
  -- CPI indices are relative to the external-account region; physical account 0 is state.
  let fromInvoke := if usesCpi program then Nat.max 3 (highest + 2) else 0
  let fromLeaves := program.methods.foldl (init := 0) fun acc method =>
    Nat.max acc (ProofForge.Ops.opsMinAccounts method.ops)
  Nat.max fromInvoke fromLeaves

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def inputLayout (program : Extract.Legacy.Program) : InputLayout :=
  inputLayoutOf (dataLen program) (usesWalk program) (cpiAccountCount program)

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def layoutSig (program : Extract.Legacy.Program) : String :=
  layoutSigOf (sourceSlots program)

def layoutPreimage (program : Extract.Legacy.Program) : String :=
  layoutPreimageOf (sourceSlots program)

def layoutMarkerHex (program : Extract.Legacy.Program) : Except String String :=
  layoutMarkerHexOf (sourceSlots program)

end ProofForge.Svm.ABI
