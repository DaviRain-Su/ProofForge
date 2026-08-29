import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Evm.Ops
import ProofForge.Evm.Codec
import ProofForge.Evm.Component
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.IR

open ProofForge.Crypto

/-- EVM instructions are owned by the EVM lowering boundary, not by the frontend Ops enum. -/
inductive Op where
  | letLocal (i : Nat) (value : Ops.Val)
  | joinLocal (i : Nat)
  | setLocal (i : Nat) (value : Ops.Val)
  | checkedAddU64 (lhs rhs : Ops.Val)
  | checkedSubU64 (lhs rhs : Ops.Val)
  | checkedMulU64 (lhs rhs : Ops.Val)
  | checkedDivU64 (lhs rhs : Ops.Val)
  | checkedModU64 (lhs rhs : Ops.Val)
  | ite (cmp : Ops.Cmp) (lhs rhs : Ops.Val) (thn els : Array Op)
  | forAccum (n : Nat) (addend : Ops.Val) (resultLocal : Nat)
  | forBody (n : Nat) (body : Array Op)
  | indexSet (name : String) (idx value : Ops.Val) (len : Nat) (elemOff : Nat := 0)
  | component (call : Component.Call Ops.Val)
  | storeField (name : String) (value : Ops.Val)
  | okState (value : Ops.Val)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Ops.Val)
  | returnState (value : Ops.Val)
  deriving BEq, Repr, Inhabited

private partial def lowerOp : Ops.Op → Except String Op
  | .letLocal i value => pure (.letLocal i value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => pure (.setLocal i value)
  | .checkedAddU64 lhs rhs => pure (.checkedAddU64 lhs rhs)
  | .checkedSubU64 lhs rhs => pure (.checkedSubU64 lhs rhs)
  | .checkedMulU64 lhs rhs => pure (.checkedMulU64 lhs rhs)
  | .checkedDivU64 lhs rhs => pure (.checkedDivU64 lhs rhs)
  | .checkedModU64 lhs rhs => pure (.checkedModU64 lhs rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp lhs rhs (← lowerOps thn) (← lowerOps els)
  | .forAccum n addend resultLocal => pure (.forAccum n addend resultLocal)
  | .forBody n body => return .forBody n (← lowerOps body)
  | .indexSetLeaf name _ _ _ leaf =>
      throw s!"extract/ir: unresolved vector leaf {name}.{leaf}"
  | .indexSet name idx value len elemOff => pure (.indexSet name idx value len elemOff)
  | .storeField name value => pure (.storeField name value)
  | .okState value => pure (.okState value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => pure (.returnU64 value)
  | .returnState value => pure (.returnState value)
  | .ext (.component call) => pure (.component call)

where
  lowerOps (ops : Array Ops.Op) : Except String (Array Op) :=
    ops.mapM lowerOp

def ofSourceOps (ops : Array Ops.Op) : Except String (Array Op) :=
  ops.mapM lowerOp

private partial def Op.toSource : Op → Ops.Op
  | .letLocal i value => .letLocal i value
  | .joinLocal i => .joinLocal i
  | .setLocal i value => .setLocal i value
  | .checkedAddU64 lhs rhs => .checkedAddU64 lhs rhs
  | .checkedSubU64 lhs rhs => .checkedSubU64 lhs rhs
  | .checkedMulU64 lhs rhs => .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs => .checkedDivU64 lhs rhs
  | .checkedModU64 lhs rhs => .checkedModU64 lhs rhs
  | .ite cmp lhs rhs thenOps elseOps =>
      .ite cmp lhs rhs (toSourceOps thenOps) (toSourceOps elseOps)
  | .forAccum bound addend resultLocal => .forAccum bound addend resultLocal
  | .forBody bound body => .forBody bound (toSourceOps body)
  | .indexSet name index value len elemOff => .indexSet name index value len elemOff
  | .component call => .ext (.component call)
  | .storeField name value => .storeField name value
  | .okState value => .okState value
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name
  | .returnU64 value => .returnU64 value
  | .returnState value => .returnState value

where
  toSourceOps (ops : Array Op) : Array Ops.Op := ops.map Op.toSource

def toSourceOps (ops : Array Op) : Array Ops.Op := ops.map Op.toSource

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt

private def mapCfgPayload (mapValue : Ops.Val → Ops.Val) :
    Ops.OpExt Ops.Val → Ops.OpExt Ops.Val
  | .component call => .component (call.mapValues mapValue)

private def cfgPayloadValues : Ops.OpExt Ops.Val → Array Ops.Val
  | .component call => call.values

def cfgDialect : Core.CFG.Dialect Ops.ValKind Ops.OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .evm kind => pure kind
  | .svm _ => throw "extract/unsupported: evm rejects svm value"

private def projectOpExt
    (projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .svm _ => throw "extract/unsupported: evm rejects svm effect"
  | .evm payload =>
      match payload with
      | .component call =>
          return .component (← call.mapValuesM projectVal)

/-- Static registration of the extractor-to-EVM projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt where
  name := "EVM"
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun method reason =>
    if reason.startsWith "extract/unsupported: evm rejects svm" then
      s!"extract/unsupported: evm rejects svm leaf in {method}"
    else reason
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := cfgDialect

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

private partial def walk (fuel : Nat) (ops : Array Op) (predicate : Op → Bool) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
      ops.any fun op =>
        predicate op ||
          match op with
          | .ite _ _ _ thn els => walk fuel' thn predicate || walk fuel' els predicate
          | .forBody _ body => walk fuel' body predicate
          | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walk 16 ops fun | .storeField .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walk 16 ops fun | .indexSet .. => true | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasEvmDeposit (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .component call => call.isDeposit
    | _ => false

def hasEvmReceive (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .component call => call.isReceive
    | _ => false

private partial def valMentionsImm : Ops.Val → Bool
  | .ext .immU64 #[] | .ext .immU64b #[]
  | .ext .immW0 #[] | .ext .immW1 #[] | .ext .immW2 #[]
  | .ext .immX0 #[] | .ext .immX1 #[] | .ext .immX2 #[] => true
  | .field base _ | .bitNot base => valMentionsImm base
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      valMentionsImm l || valMentionsImm r
  | .indexGet base _ index _ _ => valMentionsImm base || valMentionsImm index
  | .select _ l r t f =>
      valMentionsImm l || valMentionsImm r || valMentionsImm t || valMentionsImm f
  | .ext _ operands => operands.any valMentionsImm
  | _ => false

def hasImmutable (ops : Array Op) : Bool :=
  walk 16 ops fun op =>
    match op with
    | .letLocal _ v | .setLocal _ v | .storeField _ v | .okState v
    | .returnU64 v | .returnState v | .forAccum _ v _ =>
        valMentionsImm v
    | .component call => call.anyValue valMentionsImm
    | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
    | .checkedDivU64 l r | .checkedModU64 l r | .indexSet _ l r _ _ =>
        valMentionsImm l || valMentionsImm r
    | .ite _ l r _ _ => valMentionsImm l || valMentionsImm r
    | _ => false

structure Slot where
  place : Option Core.Place := none
  name : String
  index : Nat
  /-- 物理宽：1/2/4/8。EVM 仍占一个 storage word，窄值在低字节。 -/
  width : Nat := 8
  deriving BEq, Repr, Inhabited

structure VectorLeaf where
  elementPath : Array Core.PathStep := #[]
  byteOffset : Nat
  slotOffset : Nat
  width : Nat
  deriving BEq, Repr, Inhabited

/-- Physical EVM storage layout for a fixed-length source vector. -/
structure Vector where
  place : Option Core.Place := none
  name : String
  baseSlot : Nat
  length : Nat
  strideSlots : Nat
  leaves : Array VectorLeaf := #[]
  deriving BEq, Repr, Inhabited

structure Method where
  kind : Core.IR.MethodKind
  name : String
  ixName : String
  selector : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  paramTypes : Array Core.Codec.Scalar := #[]
  paramSchemas : Array Core.Codec.Schema := #[]
  retWidths : Array Nat := #[]
  retTypes : Array Core.Codec.Scalar := #[]
  retSchema : Core.Codec.Schema := .unit
  retCount : Nat := 1
  /-- Canonical identity for input guard semantics not encoded by the Solidity selector. -/
  inputPolicy : String := ""
  /-- Target-owned ABI output plan, independent of calldata-tail and input-guard state. -/
  outputPlan : Option Codec.OutputPlan := none
  /-- Canonical identity for output rules not represented in the function selector. -/
  outputPolicy : String := ""
  ops : Array Op := #[]
  evaluation : Core.Evaluation Ops.ValKind := {}
  view : Bool := false
  payable : Bool := false
  deriving BEq, Repr, Inhabited

private def resolveParamTypes (count : Nat) (types : Array Core.Codec.Scalar)
    (legacyWidths : Array Nat) : Except String (Array Core.Codec.Scalar) := do
  if types.size == count then
    unless types.all Core.Codec.Scalar.isWellFormed do
      throw "evm/codec: invalid parameter scalar metadata"
    return types
  if types.isEmpty && legacyWidths.size == count then
    return ← legacyWidths.mapM Codec.scalarOfLegacyWidth
  if types.isEmpty && legacyWidths.isEmpty then
    return Array.replicate count .uint64
  throw "evm/codec: incomplete parameter metadata"

def Method.resolvedParamTypes (method : Method) : Except String (Array Core.Codec.Scalar) :=
  resolveParamTypes method.paramCount method.paramTypes method.paramWidths

def Method.resolvedRetTypes (method : Method) : Except String (Array Core.Codec.Scalar) := do
  if let some plan := method.outputPlan then
    return plan.sourceWords
  unless method.retTypes.isEmpty do
    unless method.retTypes.all Core.Codec.Scalar.isWellFormed do
      throw "evm/codec: invalid return scalar metadata"
    return method.retTypes
  unless method.retWidths.isEmpty do
    return ← method.retWidths.mapM Codec.scalarOfLegacyWidth
  unless method.retSchema == .unit do
    return (← Codec.staticAbiLeaves method.retSchema).map (·.type)
  return Array.replicate method.retCount .uint64

private def schemaIsScalar : Core.Codec.Schema → Bool
  | .scalar _ => true
  | _ => false

def Method.logicalParamCount (method : Method) : Nat :=
  if method.paramSchemas.isEmpty then method.paramCount else method.paramSchemas.size

def Method.abiParamTypes (method : Method) : Except String (Array String) := do
  if method.paramSchemas.isEmpty then
    return ← (← method.resolvedParamTypes).mapM Codec.abiType
  method.paramSchemas.mapM fun schema => return (← Codec.inputPlan schema).typeName

private def paramWordStart (plans : Array Codec.AbiInputPlan) (index : Nat) : Nat :=
  (plans.extract 0 index).foldl (init := 0) fun count plan => count + plan.wordCount

private def rewriteAbiPayload
    (rewriteValue : Ops.Val → Except String Ops.Val) :
    Ops.OpExt Ops.Val → Except String (Ops.OpExt Ops.Val)
  | .component call => return .component (← call.mapValuesM rewriteValue)

private def rewriteAbiRoot (method : Core.IR.Method Ops.ValKind Ops.OpExt)
    (plans : Array Codec.AbiInputPlan) (physicalCount : Nat) :
    Ops.Val → Except String (Option Ops.Val)
  | .indexGet (.arg param) name index length elementOffset => do
      if param ≥ method.paramCount then return none
      let some plan := plans[param]?
        | throw "evm/codec: input ABI plan is missing"
      let some dynamic := plan.dynamic
        | return none
      let (capacity, elementWords) := dynamic.indexedFrame
      -- Generic `pf_inline` helpers can erase the host Vector's implicit Nat argument before
      -- Extract observes it, leaving the compatibility `indexGet.length` at zero. The typed ABI
      -- plan remains authoritative for capacity and the fixed local frame.
      unless name == "values" && (length == 0 || length == capacity) && elementOffset == 0 do
        throw (s!"evm/codec: dynamic index projection {name}/{length}/{elementOffset} " ++
          s!"does not match values/{capacity}/0")
      let some elementType := elementWords[0]?
        | throw "evm/codec: dynamic element plan is empty"
      unless elementWords.size == 1 && Codec.limbCount elementType == 1 do
        throw "evm/codec: dynamic reads currently require one-limb scalar elements"
      let start := paramWordStart plans param
      let mut selected : Ops.Val := .lit 0
      for i in [0:capacity] do
        selected := .select .eq index (.lit (UInt64.ofNat i)) (.arg (start + 1 + i)) selected
      return some selected
  | .field (.arg index) name => do
      if index ≥ method.paramCount then return none
      let some plan := plans[index]?
        | throw "evm/codec: input ABI plan is missing"
      let start := paramWordStart plans index
      let projection ← plan.resolveProjection name
      let some type := plan.words[projection.leafIndex]?
        | throw "evm/codec: input projection word is out of range"
      let physical := start + projection.leafIndex
      if Codec.limbCount type == 1 then
        return some (.arg physical)
      return some (.field (.arg physical) s!"w{projection.partIndex}")
  | .arg index => do
      if index < method.paramCount then
        let some plan := plans[index]?
          | throw "evm/codec: input ABI plan is missing"
        unless plan.wordCount == 1 do
          throw s!"evm/codec: aggregate parameter {index} requires a scalar projection"
        return some (.arg (paramWordStart plans index))
      if method.kind != .init && index == method.paramCount then
        return some (.arg physicalCount)
      return none
  | _ => pure none

private structure BoundParams where
  count : Nat
  widths : Array Nat
  types : Array Core.Codec.Scalar
  inputPolicy : String
  ops : Array Ops.Op

def inputPolicyOf (plans : Array Codec.AbiInputPlan) : String :=
  let policies := (plans.mapIdx fun i plan =>
    let canonical := plan.inputCanonical
    if canonical.isEmpty then none else some s!"{i}={canonical}").filterMap id
  if policies.isEmpty then "" else String.intercalate "," policies.toList

private def bindParams (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String BoundParams := do
  let hasAggregate := !method.paramSchemas.isEmpty && !method.paramSchemas.all schemaIsScalar
  if !hasAggregate then
    let widths :=
      if method.paramWidths.size == method.paramCount then method.paramWidths
      else Array.replicate method.paramCount 8
    return {
      count := method.paramCount
      widths
      types := ← resolveParamTypes method.paramCount method.paramTypes widths
      inputPolicy := ""
      ops := method.ops
    }
  unless method.paramSchemas.size == method.paramCount do
    throw s!"evm/codec: aggregate parameter schemas are incomplete for {method.ixName}"
  let plans ← method.paramSchemas.mapM Codec.inputPlan
  let types := plans.foldl (init := #[]) fun out plan => out ++ plan.words
  let ops ← Core.Target.rewriteOpsValues (rewriteAbiRoot method plans types.size)
    rewriteAbiPayload method.ops
  return {
    count := types.size
    widths := types.map (·.byteWidth)
    types
    inputPolicy := inputPolicyOf plans
    ops
  }

private structure BoundReturn where
  types : Array Core.Codec.Scalar
  plan : Option Codec.OutputPlan := none
  policy : String := ""

private def bindReturn (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String BoundReturn := do
  if let some plan ← Codec.outputPlan method.retSchema then
    let types := plan.sourceWords
    unless types.size == method.retCount do
      throw s!"evm/codec: ABI return metadata is incomplete for {method.ixName}"
    return { types, plan := some plan, policy := plan.canonical }
  if method.retSchema == .unit || schemaIsScalar method.retSchema then
    return { types := method.retTypes }
  let types := (← Codec.staticAbiLeaves method.retSchema).map (·.type)
  let sourceParts := types.foldl (init := 0) fun count type => count + Codec.limbCount type
  unless sourceParts == method.retCount do
    throw s!"evm/codec: aggregate return metadata is incomplete for {method.ixName}"
  return { types }

def Method.toCFG (method : Method) : Except String CFG := do
  let source := toSourceOps method.ops
  let graph ←
    if method.kind == .init then Core.CFG.lowerInit cfgDialect source
    else Core.CFG.lower cfgDialect source
  Core.CFG.optimize cfgDialect graph

structure Program where
  name : String
  slots : Array Slot
  vectors : Array Vector := #[]
  /-- Target-neutral source identity retained across EVM lowering. -/
  schema : Core.Schema := {}
  constructor : Method
  entries : Array Method
  deriving BEq, Repr, Inhabited

def programHasImmutable (p : Program) : Bool :=
  hasImmutable p.constructor.ops || p.entries.any (fun m => hasImmutable m.ops)

def slotIndex (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.index)

def slotWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def hasOptionLeaves (p : Program) : Bool :=
  (optionLeafNames? p).isSome

private def legacyVector (p : Program) (name : String) : Option Vector :=
  let pre0 := name ++ "_0"
  let group :=
    p.slots.filter fun slot => slot.name == pre0 || slot.name.startsWith (pre0 ++ "_")
  if group.isEmpty then none
  else
    let digitPrefix (value : String) : String :=
      Id.run do
        let mut out := ""
        for c in value.toList do
          if c.isDigit then out := out.push c else return out
        return out
    let length :=
      p.slots.foldl (init := 0) fun acc slot =>
        let rest :=
          if slot.name.startsWith (name ++ "_") then
            digitPrefix (slot.name.drop (name.length + 1) |>.copy)
          else ""
        match rest.toNat? with
        | some i => Nat.max acc (i + 1)
        | none => acc
    let baseSlot := group[0]!.index
    if length == 0 then none
    else some { name, baseSlot, length, strideSlots := group.size }

def vector? (p : Program) (name : String) : Option Vector :=
  match p.vectors.find? (·.name == name) with
  | some vector => some vector
  | none => legacyVector p name

def vectorBaseSlot (p : Program) (name : String) : Option Nat :=
  (vector? p name).map (·.baseSlot)

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given else (vector? p name).map (·.length) |>.getD 0

def vectorStrideSlots (p : Program) (name : String) : Nat :=
  (vector? p name).map (·.strideSlots) |>.getD 1

/-- Convert a byte offset within one source vector element to its EVM leaf-slot offset. -/
def vectorLeafSlotOffset (p : Program) (name : String) (byteOffset : Nat) : Nat :=
  match p.vectors.find? (·.name == name) with
  | some vector =>
      (vector.leaves.find? (·.byteOffset == byteOffset)).map (·.slotOffset)
        |>.getD vector.leaves.size
  | none => byteOffset / 8

/-- Width of the leaf at one byte offset within a source vector element. -/
def vectorLeafWidth (p : Program) (name : String) (byteOffset : Nat) : Option Nat := do
  let vector ← vector? p name
  if vector.leaves.isEmpty then
    -- Legacy fixtures only model vectors of UInt64 leaves.
    some 8
  else
    (vector.leaves.find? (·.byteOffset == byteOffset)).map (·.width)

private def rejectSlot (slot : Core.IR.Slot) : Option String :=
  if !(slot.width == 1 || slot.width == 2 || slot.width == 4 || slot.width == 8) then
    some s!"extract/unsupported: evm slot {slot.name} width {slot.width}"
  else none

private def isCtor (method : Core.IR.Method Ops.ValKind Ops.OpExt) : Bool :=
  method.kind == .init

private def lowerVectors (src : Core.IR.Program Ops.ValKind Ops.OpExt)
    (slots : Array Slot) : Array Vector :=
  src.schema.vectors.filterMap fun vector => do
    let baseSlot ← src.schema.vectorBaseLeafIndex? vector
    let _ ← slots[baseSlot]?
    let sourceLeaves := src.schema.vectorElementLeaves vector
    let leaves := sourceLeaves.mapIdx fun slotOffset leaf =>
      let byteOffset := (sourceLeaves.extract 0 slotOffset).foldl (init := 0) fun n item =>
        n + item.width
      ({
        elementPath := leaf.place.steps.extract (vector.place.steps.size + 1)
        byteOffset
        slotOffset
        width := leaf.width
      } : VectorLeaf)
    return {
      place := some vector.place
      name := vector.name
      baseSlot
      length := vector.length
      strideSlots := vector.elementLeaves
      leaves
    }

private def lowerMethodBody (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String (BoundParams × Array Op × Core.Evaluation Ops.ValKind) := do
  let params ← bindParams method
  return (params, ← ofSourceOps params.ops, method.evaluation)

/-- Project the combined extractor dialect and lower it into an EVM-owned physical program. -/
def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  for method in src.methods do
    unless method.annotations.isEmpty do
      throw s!"extract/unsupported: evm cannot consume target annotations on {method.ixName}"
  let source ← Core.Target.projectProgram extractRegistration src
  if source.slots.isEmpty then
    throw "extract/unsupported: evm program has no slots"
  for slot in source.slots do
    if let some reason := rejectSlot slot then
      throw reason
  let mut ctors : Array (Core.IR.Method Ops.ValKind Ops.OpExt) := #[]
  let mut extras : Array (Core.IR.Method Ops.ValKind Ops.OpExt) := #[]
  for method in source.methods do
    if isCtor method then
      ctors := ctors.push method
    else
      extras := extras.push method
  if ctors.isEmpty then
    throw "extract/unsupported: evm wants a constructor"
  let ctorSrc :=
    match ctors.find? (fun m =>
        m.ixName == "initialize" || Core.IR.lastName m.name == "init") with
    | some m => m
    | none => ctors[0]!
  -- EVM initialization is deployment-only. Alternative source initializers may remain useful to
  -- targets such as SVM, but exposing them as runtime selectors would allow storage reinitialization.
  let rest := extras
  if rest.isEmpty then
    throw "extract/unsupported: evm wants at least one entry"
  if ctorSrc.ops.isEmpty then
    throw "extract/unsupported: init missing returnState"
  unless ctorSrc.ops.any (fun | .returnState _ => true | _ => false) do
    throw "extract/unsupported: init missing returnState"
  let (ctorParams, ctorOps, ctorEvaluation) ← lowerMethodBody ctorSrc
  let ctorReturn ← bindReturn ctorSrc
  let ctor : Method := {
    kind := ctorSrc.kind
    name := ctorSrc.name
    ixName := ctorSrc.ixName
    selector := ""
    paramCount := ctorParams.count
    paramWidths := ctorParams.widths
    paramTypes := ctorParams.types
    paramSchemas := ctorSrc.paramSchemas
    retWidths := ctorSrc.retWidths
    retTypes := ctorReturn.types
    retSchema := ctorSrc.retSchema
    retCount := 1
    inputPolicy := ctorParams.inputPolicy
    outputPlan := ctorReturn.plan
    outputPolicy := ctorReturn.policy
    ops := ctorOps
    evaluation := ctorEvaluation
    view := false
    payable := false
  }
  let mut entries : Array Method := #[]
  for m in rest do
    if m.ops.isEmpty then
      throw s!"extract/unsupported: empty ops {m.ixName}"
    let (params, ops, evaluation) ← lowerMethodBody m
    let abiTypes ←
      if m.paramSchemas.isEmpty then params.types.mapM Codec.abiType
      else m.paramSchemas.mapM fun schema => return (← Codec.inputPlan schema).typeName
    let sel := Keccak.selector m.ixName abiTypes
    let view := m.kind == .get
    let returns ← bindReturn m
    entries := entries.push {
      kind := m.kind
      name := m.name
      ixName := m.ixName
      selector := sel
      paramCount := params.count
      paramWidths := params.widths
      paramTypes := params.types
      paramSchemas := m.paramSchemas
      retWidths := m.retWidths
      retTypes := returns.types
      retSchema := m.retSchema
      retCount := m.retCount
      inputPolicy := params.inputPolicy
      outputPlan := returns.plan
      outputPolicy := returns.policy
      ops
      evaluation
      view
      payable := !view && (hasEvmDeposit ops || hasEvmReceive ops)
    }
  let slots := source.slots.mapIdx fun i s =>
    { place := (source.schema.leaves[i]?).map (·.place), name := s.name, index := i,
      width := s.width }
  return {
    name := source.name
    slots
    vectors := lowerVectors source slots
    schema := source.schema
    constructor := ctor
    entries
  }

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

/-- Preserve the old closed-union spelling in canonical digests during the IR migration. -/
private def legacyCmpRepr (cmp : Ops.Cmp) : String :=
  "ProofForge.Ops.Cmp." ++ cmpTag cmp

private partial def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valCanon b})"
  | .ext .caller #[] => "ecall"
  | .ext .blockNumber #[] => "eblk"
  | .ext .timestamp #[] => "ets"
  | .ext .chainId #[] => "echain"
  | .ext .self #[] => "eself"
  | .ext .callValue #[] => "eval"
  | .ext .selfBalance #[] => "ebal"
  | .ext .callerW0 #[] => "ecw0"
  | .ext .callerW1 #[] => "ecw1"
  | .ext .callerW2 #[] => "ecw2"
  | .ext .selfW0 #[] => "esw0"
  | .ext .selfW1 #[] => "esw1"
  | .ext .selfW2 #[] => "esw2"
  | .ext .immU64 #[] => "eimm"
  | .ext .immU64b #[] => "eimmb"
  | .ext .immW0 #[] => "eiw0"
  | .ext .immW1 #[] => "eiw1"
  | .ext .immW2 #[] => "eiw2"
  | .ext .immX0 #[] => "eix0"
  | .ext .immX1 #[] => "eix1"
  | .ext .immX2 #[] => "eix2"
  | .ext (.gasLeft256 limb) #[] => s!"egas.{limb}"
  | .ext (.baseFee256 limb) #[] => s!"ebasefee.{limb}"
  | .ext (.prevRandao256 limb) #[] => s!"erandao.{limb}"
  | .ext (.gasLimit256 limb) #[] => s!"egaslimit.{limb}"
  | .bitAnd l r => s!"and({valCanon l},{valCanon r})"
  | .bitOr l r => s!"or({valCanon l},{valCanon r})"
  | .bitXor l r => s!"xor({valCanon l},{valCanon r})"
  | .bitNot v => s!"not({valCanon v})"
  | .shiftL l r => s!"shl({valCanon l},{valCanon r})"
  | .shiftR l r => s!"shr({valCanon l},{valCanon r})"
  | .indexGet b n i k off =>
      if off == 0 then s!"idx.{n}[{valCanon i}/{k}]({valCanon b})"
      else s!"idx.{n}+{off}[{valCanon i}/{k}]({valCanon b})"
  | .loopIx => "ix"
  | .select c l r t f =>
      s!"sel.{legacyCmpRepr c}({valCanon l},{valCanon r},{valCanon t},{valCanon f})"
  | .addU64 l r => s!"uadd({valCanon l},{valCanon r})"
  | .subU64 l r => s!"usub({valCanon l},{valCanon r})"
  | .mulU64 l r => s!"umul({valCanon l},{valCanon r})"
  | .divU64 l r => s!"udiv({valCanon l},{valCanon r})"
  | .modU64 l r => s!"umod({valCanon l},{valCanon r})"
  | .ext (.component query) operands => query.canonical valCanon operands
  | .ext kind operands =>
      s!"ext.{repr kind}({String.intercalate "," (operands.map valCanon).toList})"

private partial def opsCanon (ops : Array Op) : String :=
  let rec one (op : Op) : String :=
    match op with
    | .letLocal i v => s!"let.{i}({valCanon v})"
    | .joinLocal i => s!"join.{i}"
    | .setLocal i v => s!"set.{i}({valCanon v})"
    | .checkedAddU64 l r => s!"add({valCanon l},{valCanon r})"
    | .checkedSubU64 l r => s!"sub({valCanon l},{valCanon r})"
    | .checkedMulU64 l r => s!"mul({valCanon l},{valCanon r})"
    | .checkedDivU64 l r => s!"div({valCanon l},{valCanon r})"
    | .checkedModU64 l r => s!"mod({valCanon l},{valCanon r})"
    | .ite c l r t f => s!"ite.{cmpTag c}({valCanon l},{valCanon r},[{opsCanon t}],[{opsCanon f}])"
    | .forAccum n v resultLocal => s!"for.{resultLocal}({n},{valCanon v})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet n i v k off =>
        if off == 0 then s!"iset.{n}[{valCanon i}/{k}]({valCanon v})"
        else s!"iset.{n}+{off}[{valCanon i}/{k}]({valCanon v})"
    | .component call => call.canonical valCanon
    | .storeField n v => s!"st.{n}({valCanon v})"
    | .okState v => s!"ok({valCanon v})"
    | .errorOverflow => "ovf"
    | .errorNamed n => s!"err.{n}"
    | .returnU64 v => s!"retu({valCanon v})"
    | .returnState v => s!"rets({valCanon v})"
  String.intercalate ";" (ops.toList.map one)

def canonical (p : Program) : String :=
  let slots := String.intercalate ","
    (p.slots.map (fun s => s!"{s.name}:{s.width}")).toList
  let ctorPolicy := if p.constructor.inputPolicy.isEmpty then ""
    else s!":{p.constructor.inputPolicy}"
  let ctorOutput := if p.constructor.outputPolicy.isEmpty then ""
    else s!":{p.constructor.outputPolicy}"
  let ctor := s!"ctor:{p.constructor.paramCount}{ctorPolicy}{ctorOutput}:[{opsCanon p.constructor.ops}]"
  let entries :=
    (p.entries.qsort (fun a b => a.ixName < b.ixName)).toList.map fun m =>
      let tag := if m.view then "view" else if m.payable then "pay" else "mut"
      let policy := if m.inputPolicy.isEmpty then "" else s!":{m.inputPolicy}"
      let output := if m.outputPolicy.isEmpty then "" else s!":{m.outputPolicy}"
      let base := s!"{tag}:{m.ixName}:{m.selector}:{m.paramCount}{policy}{output}"
      if (m.paramWidths.isEmpty || m.paramWidths.all (· == 8)) &&
          m.retCount == 1 && m.retWidths.isEmpty then
        s!"{base}:[{opsCanon m.ops}]"
      else
        let widths := String.intercalate "," (m.paramWidths.map toString).toList
        if m.retWidths.isEmpty then
          s!"{base}:{widths}:r{m.retCount}:[{opsCanon m.ops}]"
        else
          let rws := String.intercalate "," (m.retWidths.map toString).toList
          s!"{base}:{widths}:r{m.retCount}:{rws}:[{opsCanon m.ops}]"
  s!"evm|{p.name}|{slots}|{ctor}|{String.intercalate "/" entries}"

def digestHex (p : Program) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical p))

end ProofForge.Evm.IR
