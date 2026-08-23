import ProofForge.Core.IR
import ProofForge.Svm.ABI

namespace ProofForge.Svm.IR

/-- SVM instructions are lowered separately from the frontend compatibility Ops. -/
inductive Op where
  | letLocal (i : Nat) (value : Ops.Val)
  | checkedAddU64 (lhs rhs : Ops.Val)
  | checkedSubU64 (lhs rhs : Ops.Val)
  | checkedMulU64 (lhs rhs : Ops.Val)
  | checkedDivU64 (lhs rhs : Ops.Val)
  | checkedModU64 (lhs rhs : Ops.Val)
  | ite (cmp : Ops.Cmp) (lhs rhs : Ops.Val) (thn els : Array Op)
  | invoke (programIx : Nat) (metas : Array Ops.CpiMeta) (data : Array Ops.CpiWord)
      (seed : Option String := none) (bump : Option Ops.Val := none)
  | forAccum (n : Nat) (addend : Ops.Val)
  | forBody (n : Nat) (body : Array Op)
  | indexSet (name : String) (idx value : Ops.Val) (len : Nat) (elemOff : Nat := 0)
  | storeField (name : String) (value : Ops.Val)
  | okState (value : Ops.Val)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Ops.Val)
  | returnState (value : Ops.Val)
  deriving BEq, Repr, Inhabited

private partial def lowerOp : Ops.Op → Except String Op
  | .letLocal i value => pure (.letLocal i value)
  | .checkedAddU64 lhs rhs => pure (.checkedAddU64 lhs rhs)
  | .checkedSubU64 lhs rhs => pure (.checkedSubU64 lhs rhs)
  | .checkedMulU64 lhs rhs => pure (.checkedMulU64 lhs rhs)
  | .checkedDivU64 lhs rhs => pure (.checkedDivU64 lhs rhs)
  | .checkedModU64 lhs rhs => pure (.checkedModU64 lhs rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp lhs rhs (← lowerOps thn) (← lowerOps els)
  | .invoke programIx metas data seed bump => pure (.invoke programIx metas data seed bump)
  | .forAccum n addend => pure (.forAccum n addend)
  | .forBody n body => return .forBody n (← lowerOps body)
  | .indexSet name idx value len elemOff => pure (.indexSet name idx value len elemOff)
  | .storeField name value => pure (.storeField name value)
  | .okState value => pure (.okState value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => pure (.returnU64 value)
  | .returnState value => pure (.returnState value)
  | .evmDeposit _ | .evmSendEth .. | .evmLog ..
  | .mapGetU64 .. | .mapSetU64 .. | .mapGetAddr .. | .mapSetAddr ..
  | .mapGetPair .. | .mapSetPair ..
  | .evmTokenTransfer .. | .evmTokenBalanceOfSelf .. =>
      throw "extract/unsupported: svm rejects evm leaf"

where
  lowerOps (ops : Array Ops.Op) : Except String (Array Op) :=
    ops.mapM lowerOp

def ofSourceOps (ops : Array Ops.Op) : Except String (Array Op) :=
  ops.mapM lowerOp

private partial def Op.toSource : Op → Ops.Op
  | .letLocal i value => .letLocal i value
  | .checkedAddU64 lhs rhs => .checkedAddU64 lhs rhs
  | .checkedSubU64 lhs rhs => .checkedSubU64 lhs rhs
  | .checkedMulU64 lhs rhs => .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs => .checkedDivU64 lhs rhs
  | .checkedModU64 lhs rhs => .checkedModU64 lhs rhs
  | .ite cmp lhs rhs thn els => .ite cmp lhs rhs (toSourceOps thn) (toSourceOps els)
  | .invoke programIx metas data seed bump => .invoke programIx metas data seed bump
  | .forAccum n addend => .forAccum n addend
  | .forBody n body => .forBody n (toSourceOps body)
  | .indexSet name idx value len elemOff => .indexSet name idx value len elemOff
  | .storeField name value => .storeField name value
  | .okState value => .okState value
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name
  | .returnU64 value => .returnU64 value
  | .returnState value => .returnState value

where
  toSourceOps (ops : Array Op) : Array Ops.Op :=
    ops.map Op.toSource

def toSourceOps (ops : Array Op) : Array Ops.Op :=
  ops.map Op.toSource

def hasStoreField (ops : Array Op) : Bool :=
  Ops.hasStoreField (toSourceOps ops)

def hasIndexSet (ops : Array Op) : Bool :=
  Ops.hasIndexSet (toSourceOps ops)

def hasCheckedArith (ops : Array Op) : Bool :=
  Ops.hasCheckedArith (toSourceOps ops)

def hasSelect (ops : Array Op) : Bool :=
  Ops.hasSelect (toSourceOps ops)

def hasInvoke (ops : Array Op) : Bool :=
  Ops.hasInvoke (toSourceOps ops)

structure Method where
  kind : Core.IR.MethodKind
  name : String
  ixName : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  retCount : Nat := 1
  ops : Array Op := #[]
  evaluation : Core.Evaluation := {}
  deriving BEq, Repr, Inhabited

/-- A statically addressed SVM account-data cell. Offsets include the eight-byte layout marker. -/
structure Slot where
  place : Option Core.Place := none
  name : String
  offset : Nat
  width : Nat
  abi : String
  deriving BEq, Repr, Inhabited

structure VectorLeaf where
  elementPath : Array Core.PathStep := #[]
  offset : Nat
  width : Nat
  deriving BEq, Repr, Inhabited

/-- Physical SVM layout for a fixed-length source vector. -/
structure Vector where
  place : Option Core.Place := none
  name : String
  baseOffset : Nat
  length : Nat
  strideBytes : Nat
  leaves : Array VectorLeaf := #[]
  deriving BEq, Repr, Inhabited

structure Program where
  name : String
  slots : Array Slot
  vectors : Array Vector := #[]
  schema : Core.Schema := {}
  methods : Array Method
  /-- Retained only for protocol metadata and stable pre-existing digests. -/
  source : Core.IR.Program
  deriving BEq, Repr, Inhabited

private def lowerSlots (src : Core.IR.Program) : Array Slot := Id.run do
  let mut result := #[]
  let mut offset := 8
  for i in [0:src.slots.size] do
    let slot := src.slots[i]!
    result := result.push {
      place := (src.schema.leaves[i]?).map (·.place)
      name := slot.name
      offset
      width := slot.width
      abi := slot.abi
    }
    offset := offset + slot.width
  return result

private def lowerVectors (src : Core.IR.Program) (slots : Array Slot) : Array Vector :=
  src.schema.vectors.filterMap fun vector => do
    let baseIndex ← src.schema.vectorBaseLeafIndex? vector
    let base ← slots[baseIndex]?
    let sourceLeaves := src.schema.vectorElementLeaves vector
    let leaves := sourceLeaves.mapIdx fun index leaf =>
      let offset := (sourceLeaves.extract 0 index).foldl (init := 0) fun n item =>
        n + item.width
      ({
        elementPath := leaf.place.steps.extract (vector.place.steps.size + 1)
        offset
        width := leaf.width
      } : VectorLeaf)
    return {
      place := some vector.place
      name := vector.name
      baseOffset := base.offset
      length := vector.length
      strideBytes := vector.elementBytes
      leaves
    }

private def lowerMethod (method : Core.IR.Method) : Except String Method := do
  if Ops.hasEvmEffect method.ops then
    throw "extract/unsupported: svm rejects evm leaf"
  return {
    kind := method.kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    retCount := method.retCount
    ops := ← ofSourceOps method.ops
    evaluation := method.evaluation
  }

/-- Lower source metadata and compatibility Ops into an SVM-owned physical program. -/
def fromProgram (src : Core.IR.Program) : Except String Program := do
  let slots := lowerSlots src
  return {
    name := src.name
    slots
    vectors := lowerVectors src slots
    schema := src.schema
    methods := ← src.methods.mapM lowerMethod
    source := src
  }

def Program.fields (p : Program) : Array String :=
  p.slots.map (·.name)

def fieldOffset (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.offset)

def fieldWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

private def vector? (p : Program) (name : String) : Option Vector :=
  p.vectors.find? (·.name == name)

def vectorBaseOffset (p : Program) (name : String) : Option Nat :=
  match vector? p name with
  | some vector => some vector.baseOffset
  | none => ABI.vectorBaseOffset p.source name

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given
  else
    match vector? p name with
    | some vector => vector.length
    | none => ABI.vectorLenOf p.source name given

def vectorStride (p : Program) (name : String) : Nat :=
  match vector? p name with
  | some vector => vector.strideBytes
  | none => ABI.vectorStride p.source name

def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => Core.IR.optionLeafNames? p.source

def isProgramShape (p : Program) : Bool :=
  Core.IR.isProgramShape p.source

def usesCpi (p : Program) : Bool :=
  p.methods.any (hasInvoke ·.ops)

def usesWalk (p : Program) : Bool :=
  usesCpi p || p.methods.any fun method => Ops.hasAcc1 (toSourceOps method.ops)

def cpiAccountCount (p : Program) : Nat :=
  ABI.cpiAccountCount p.source

def dataLen (p : Program) : Nat :=
  ABI.dataLen p.source

def inputLayout (p : Program) : ABI.InputLayout :=
  ABI.inputLayout p.source

def layoutMarkerHex (p : Program) : Except String String :=
  ABI.layoutMarkerHex p.source

def digestHex (p : Program) : String :=
  Core.IR.digestHex p.source

def discHex (m : Method) : Except String String :=
  ABI.discHex {
    kind := m.kind
    name := m.name
    ixName := m.ixName
    paramCount := m.paramCount
    paramWidths := m.paramWidths
    retCount := m.retCount
    ops := toSourceOps m.ops
    evaluation := m.evaluation
  }

def lastName := Core.IR.lastName
def ixNameOfLean := Core.IR.ixNameOfLean
def u64Hex := Core.IR.u64Hex

end ProofForge.Svm.IR
