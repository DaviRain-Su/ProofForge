import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Svm.ABI
import ProofForge.Svm.Component
import ProofForge.Svm.EntryAdapter

namespace ProofForge.Svm.IR

/-- SVM instructions are lowered separately from the target-owned source Ops. -/
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
  | invoke (programIx : Nat) (metas : Array Ops.CpiMeta)
      (data : Array (Ops.CpiWord Ops.Val))
      (seeds : Array Ops.PdaSeed := #[]) (bump : Option Ops.Val := none)
  | component (call : Component.Call Ops.Val)
  | forAccum (n : Nat) (addend : Ops.Val) (resultLocal : Nat)
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
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => pure (.setLocal i value)
  | .checkedAddU64 lhs rhs => pure (.checkedAddU64 lhs rhs)
  | .checkedSubU64 lhs rhs => pure (.checkedSubU64 lhs rhs)
  | .checkedMulU64 lhs rhs => pure (.checkedMulU64 lhs rhs)
  | .checkedDivU64 lhs rhs => pure (.checkedDivU64 lhs rhs)
  | .checkedModU64 lhs rhs => pure (.checkedModU64 lhs rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp lhs rhs (← lowerOps thn) (← lowerOps els)
  | .ext (.invoke programIx metas data seed bump) =>
      pure (.invoke programIx metas data seed bump)
  | .ext (.component call) => pure (.component call)
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
  | .ite cmp lhs rhs thn els => .ite cmp lhs rhs (toSourceOps thn) (toSourceOps els)
  | .invoke programIx metas data seed bump => .ext (.invoke programIx metas data seed bump)
  | .component call => .ext (.component call)
  | .forAccum n addend resultLocal => .forAccum n addend resultLocal
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

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt

private def mapCfgPayload (mapValue : Ops.Val → Ops.Val) :
    Ops.OpExt Ops.Val → Ops.OpExt Ops.Val
  | .invoke programIx metas data seeds bump =>
      .invoke programIx metas (data.map (Ops.CpiWord.map mapValue)) seeds (bump.map mapValue)
  | .component call => .component (call.mapValues mapValue)

private def cfgPayloadValues : Ops.OpExt Ops.Val → Array Ops.Val
  | .invoke _ _ data _ bump =>
      data.filterMap Ops.CpiWord.value? ++ match bump with
        | some value => #[value]
        | none => #[]
  | .component call => call.values

def cfgDialect : Core.CFG.Dialect Ops.ValKind Ops.OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .svm kind => pure kind
  | .evm _ => throw "extract/unsupported: svm rejects evm value"

private def projectCpiWord
    (projectVal : Extract.IR.Val → Except String Ops.Val) :
    Ops.CpiWord Extract.IR.Val → Except String (Ops.CpiWord Ops.Val)
  | .u8le value => return .u8le (← projectVal value)
  | .u16le value => return .u16le (← projectVal value)
  | .u32le value => return .u32le (← projectVal value)
  | .u64le value => return .u64le (← projectVal value)
  | .selfEntry tag authoritySeed => pure (.selfEntry tag authoritySeed)
  | .ascii value => pure (.ascii value)
  | .programId => pure .programId
  | .accKey i => pure (.accKey i)

private def projectOpExt
    (projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .svm (.invoke programIx metas data seeds bump) =>
      return .invoke programIx metas (← data.mapM (projectCpiWord projectVal))
        seeds (← bump.mapM projectVal)
  | .svm (.component call) =>
      return .component (← call.mapValuesM projectVal)
  | .evm _ => throw "extract/unsupported: svm rejects evm effect"

/-- Static registration of the extractor-to-SVM projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt where
  name := "SVM"
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun _ reason =>
    if reason.startsWith "extract/unsupported: svm rejects evm" then
      "extract/unsupported: svm rejects evm leaf"
    else reason
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := cfgDialect

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

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
  paramTypes : Array Core.Codec.Scalar := #[]
  paramSchemas : Array Core.Codec.Schema := #[]
  retWidths : Array Nat := #[]
  retTypes : Array Core.Codec.Scalar := #[]
  retSchema : Core.Codec.Schema := .unit
  retCount : Nat := 1
  entry : EntryAdapter.MethodEntry := .generated
  ops : Array Op := #[]
  evaluation : Core.Evaluation Ops.ValKind := {}
  deriving BEq, Repr, Inhabited

private def rawLimbIndex : String → Option Nat
  | "w0" => some 0
  | "w1" => some 1
  | "w2" => some 2
  | "w3" => some 3
  | _ => none

private def schemaIsScalar : Core.Codec.Schema → Bool
  | .scalar _ => true
  | _ => false

private def resolveBorshProjection (plan : EntryAdapter.BorshPlan) (name : String) :
    Except String (Nat × Nat) := do
  let mut found : Array (Nat × Nat) := #[]
  for projection in plan.projections do
    if name == projection.sourceName && projection.partCount == 1 then
      found := found.push (projection.localStart, 0)
    else if !projection.sourceName.isEmpty &&
        name.startsWith (projection.sourceName ++ "_") then
      let suffix := name.drop (projection.sourceName.length + 1) |>.copy
      if let some part := rawLimbIndex suffix then
        if part < projection.partCount then
          found := found.push (projection.localStart, part)
  unless found.size == 1 do
    let shown := if name.isEmpty then "<parameter>" else name
    throw s!"extract/unsupported: Borsh projection {shown} is missing or ambiguous"
  return found[0]!

private def rawAggregateProjection (schemas : Array Core.Codec.Schema)
    (entry : EntryAdapter.RawEntry) (index : Nat) (name : String) :
    Except String (Nat × Nat) := do
  if let some plan := entry.paramBorshPlans[index]? then
    let (localStart, part) ← resolveBorshProjection plan name
    return (entry.paramLeafStart index + localStart, part)
  let some schema := schemas[index]?
    | throw "extract/unsupported: raw aggregate parameter schema is missing"
  let leaves ← EntryAdapter.staticBorshLeaves schema
  let projection ← Core.Codec.resolveSourceProjection (leaves.map (·.logical))
    (leaves.map (·.widths.size)) rawLimbIndex name
  let relative := (leaves.extract 0 projection.leafIndex).foldl (init := 0)
    fun count leaf => count + leaf.widths.size
  return (entry.paramLeafStart index + relative, projection.partIndex)

private partial def rewriteRawArg (schemas : Array Core.Codec.Schema)
    (entry : EntryAdapter.RawEntry) (base : Nat) :
    Ops.Val → Except String Ops.Val
  | .indexGet (.arg param) name index length elementOffset => do
      unless param < entry.logicalParamCount do
        throw "extract/unsupported: raw entry cannot access managed State"
      let some schema := schemas[param]?
        | throw "extract/unsupported: raw aggregate parameter schema is missing"
      let capacity? := match schema with
        | .boundedArray capacity (.scalar _) => some capacity
        | .boundedBytes capacity | .boundedString capacity => some capacity
        | _ => none
      let some capacity := capacity?
        | throw "extract/unsupported: dynamic Borsh reads require scalar bounded values"
      unless entry.usesSchemaBorsh && name == "values" &&
          (length == 0 || length == capacity) && elementOffset == 0 do
        throw "extract/unsupported: bounded index projection does not match its Borsh plan"
      let index ← rewriteRawArg schemas entry base index
      let mut selected : Ops.Val := .lit 0
      for i in [0:capacity] do
        let (localStart, part) ← rawAggregateProjection schemas entry param s!"values_{i}"
        unless part == 0 do
          throw "extract/unsupported: dynamic Borsh reads currently require one-limb elements"
        selected := .select .eq index (.lit (UInt64.ofNat i)) (.local (base + localStart)) selected
      return selected
  | .arg index => do
      unless index < entry.logicalParamCount do
        throw "extract/unsupported: raw entry cannot access managed State"
      if entry.usesSchemaBorsh then
        let (localStart, part) ← rawAggregateProjection schemas entry index ""
        return .local (base + localStart + part)
      if schemas.size == entry.logicalParamCount && !schemaIsScalar schemas[index]! then
        throw s!"extract/unsupported: raw aggregate parameter {index} requires a scalar projection"
      unless entry.paramLeafCount index == 1 do
        throw s!"extract/unsupported: raw multi-limb parameter {index} requires a limb projection"
      return .local (base + entry.paramLeafStart index)
  | .local index => pure (.local index)
  | .field (.arg index) name => do
      unless index < entry.logicalParamCount do
        throw "extract/unsupported: raw entry cannot access managed State"
      if entry.usesSchemaBorsh ||
          (schemas.size == entry.logicalParamCount && !schemaIsScalar schemas[index]!) then
        let (leafStart, limb) ← rawAggregateProjection schemas entry index name
        return .local (base + leafStart + limb)
      let some limb := rawLimbIndex name
        | throw s!"extract/unsupported: raw boundary value has unsupported projection {name}"
      unless limb < entry.paramLeafCount index do
        throw s!"extract/unsupported: raw boundary projection {name} is out of range"
      return .local (base + entry.paramLeafStart index + limb)
  | .field value name => return .field (← rewriteRawArg schemas entry base value) name
  | .lit value => pure (.lit value)
  | .bitAnd lhs rhs =>
      return .bitAnd (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .bitOr lhs rhs =>
      return .bitOr (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .bitXor lhs rhs =>
      return .bitXor (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .bitNot value => return .bitNot (← rewriteRawArg schemas entry base value)
  | .shiftL lhs rhs =>
      return .shiftL (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .shiftR lhs rhs =>
      return .shiftR (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .indexGet value name index len offset =>
      return .indexGet (← rewriteRawArg schemas entry base value) name
        (← rewriteRawArg schemas entry base index) len offset
  | .loopIx => pure .loopIx
  | .select cmp lhs rhs thn els =>
      return .select cmp (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs) (← rewriteRawArg schemas entry base thn)
        (← rewriteRawArg schemas entry base els)
  | .addU64 lhs rhs =>
      return .addU64 (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .subU64 lhs rhs =>
      return .subU64 (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .mulU64 lhs rhs =>
      return .mulU64 (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .divU64 lhs rhs =>
      return .divU64 (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .modU64 lhs rhs =>
      return .modU64 (← rewriteRawArg schemas entry base lhs) (← rewriteRawArg schemas entry base rhs)
  | .ext kind operands =>
      return .ext kind (← operands.mapM (rewriteRawArg schemas entry base))

private def rewriteRawCpiWord (schemas : Array Core.Codec.Schema)
    (entry : EntryAdapter.RawEntry) (base : Nat) :
    Ops.CpiWord Ops.Val → Except String (Ops.CpiWord Ops.Val)
  | .u8le value => return .u8le (← rewriteRawArg schemas entry base value)
  | .u16le value => return .u16le (← rewriteRawArg schemas entry base value)
  | .u32le value => return .u32le (← rewriteRawArg schemas entry base value)
  | .u64le value => return .u64le (← rewriteRawArg schemas entry base value)
  | .selfEntry tag seed => pure (.selfEntry tag seed)
  | .ascii value => pure (.ascii value)
  | .programId => pure .programId
  | .accKey index => pure (.accKey index)

private def rewriteRawPayload (schemas : Array Core.Codec.Schema)
    (entry : EntryAdapter.RawEntry) (base : Nat) :
    Ops.OpExt Ops.Val → Except String (Ops.OpExt Ops.Val)
  | .invoke programIx metas data seeds bump =>
      return .invoke programIx metas (← data.mapM (rewriteRawCpiWord schemas entry base)) seeds
        (← bump.mapM (rewriteRawArg schemas entry base))
  | .component call =>
      return .component (← call.mapValuesM (rewriteRawArg schemas entry base))

private partial def rewriteRawArgsInOp (schemas : Array Core.Codec.Schema)
    (entry : EntryAdapter.RawEntry) (base : Nat) :
    Ops.Op → Except String Ops.Op
  | .letLocal index value => return .letLocal index (← rewriteRawArg schemas entry base value)
  | .joinLocal index => pure (.joinLocal index)
  | .setLocal index value => return .setLocal index (← rewriteRawArg schemas entry base value)
  | .checkedAddU64 lhs rhs =>
      return .checkedAddU64 (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
  | .checkedSubU64 lhs rhs =>
      return .checkedSubU64 (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
  | .checkedMulU64 lhs rhs =>
      return .checkedMulU64 (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
  | .checkedDivU64 lhs rhs =>
      return .checkedDivU64 (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
  | .checkedModU64 lhs rhs =>
      return .checkedModU64 (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp (← rewriteRawArg schemas entry base lhs)
        (← rewriteRawArg schemas entry base rhs)
        (← thn.mapM (rewriteRawArgsInOp schemas entry base))
        (← els.mapM (rewriteRawArgsInOp schemas entry base))
  | .forAccum count addend result =>
      return .forAccum count (← rewriteRawArg schemas entry base addend) result
  | .forBody count body =>
      return .forBody count (← body.mapM (rewriteRawArgsInOp schemas entry base))
  | .indexSetLeaf name index value len leaf =>
      return .indexSetLeaf name (← rewriteRawArg schemas entry base index)
        (← rewriteRawArg schemas entry base value) len leaf
  | .indexSet name index value len offset =>
      return .indexSet name (← rewriteRawArg schemas entry base index)
        (← rewriteRawArg schemas entry base value) len offset
  | .storeField name value =>
      return .storeField name (← rewriteRawArg schemas entry base value)
  | .okState value => return .okState (← rewriteRawArg schemas entry base value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => return .returnU64 (← rewriteRawArg schemas entry base value)
  | .returnState value => return .returnState (← rewriteRawArg schemas entry base value)
  | .ext payload => return .ext (← rewriteRawPayload schemas entry base payload)

private partial def opLocalIds : Ops.Op → Array Nat
  | .letLocal index value | .setLocal index value => #[index] ++ Core.CFG.valueLocalIds value
  | .joinLocal index => #[index]
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      Core.CFG.valueLocalIds lhs ++ Core.CFG.valueLocalIds rhs
  | .ite _ lhs rhs thn els =>
      Core.CFG.valueLocalIds lhs ++ Core.CFG.valueLocalIds rhs ++
        thn.flatMap opLocalIds ++ els.flatMap opLocalIds
  | .forAccum _ addend result => #[result] ++ Core.CFG.valueLocalIds addend
  | .forBody _ body => body.flatMap opLocalIds
  | .indexSetLeaf _ index value _ _ | .indexSet _ index value _ _ =>
      Core.CFG.valueLocalIds index ++ Core.CFG.valueLocalIds value
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      Core.CFG.valueLocalIds value
  | .errorOverflow | .errorNamed _ => #[]
  | .ext payload => (cfgPayloadValues payload).flatMap Core.CFG.valueLocalIds

def Method.rawArgLocalBase (method : Method) : Nat :=
  method.ops.map Op.toSource |>.flatMap opLocalIds |>.foldl (init := 0) fun next index =>
    Nat.max next (index + 1)

/-- Lower a target-owned SVM method to the shared basic-block representation consumed by
code generation. This deliberately happens after target projection, so no combined EVM/SVM
extension can cross the backend boundary. -/
def Method.toCFG (method : Method) : Except String CFG := do
  let source := toSourceOps method.ops
  let source ←
    match method.entry with
    | .generated => pure source
    | .raw entry =>
        source.mapM (rewriteRawArgsInOp method.paramSchemas entry method.rawArgLocalBase)
  let graph ←
    if method.kind == .init then Core.CFG.lowerInit cfgDialect source
    else Core.CFG.lower cfgDialect source
  Core.CFG.optimize cfgDialect graph

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
  /-- Emitter-only method view used by protocol adapters with a different account contract. -/
  accountCountOverride : Option Nat := none
  deriving BEq, Repr, Inhabited

private partial def rawSelfEntriesIn (ops : Array Op) :
    Except String (Array Ops.RawSelfEntry) := do
  let mut result := #[]
  for op in ops do
    match op with
    | .invoke _ metas data seeds bump =>
        let entries := data.filterMap Ops.CpiWord.rawSelfEntry?
        unless entries.isEmpty do
          match data[0]?, entries[0]?, metas.toList, seeds.toList, bump with
          | some (Ops.CpiWord.selfEntry tag authoritySeed), some entry,
              [authorityMeta], [.ascii signerSeed], some _ =>
              unless entries.size == 1 && entry.tag == tag &&
                  entry.authoritySeed == authoritySeed && signerSeed == authoritySeed &&
                  authorityMeta.signer && !authorityMeta.writable do
                throw "extract/unsupported: malformed raw self-entry invocation"
              result := result.push entry
          | _, _, _, _, _ =>
              throw "extract/unsupported: malformed raw self-entry invocation"
    | .ite _ _ _ thn els =>
        result := result ++ (← rawSelfEntriesIn thn) ++ (← rawSelfEntriesIn els)
    | .forBody _ body => result := result ++ (← rawSelfEntriesIn body)
    | .component call =>
        for (tag, authoritySeed) in call.rawSelfEntries do
          result := result.push { tag := UInt64.ofNat tag, authoritySeed }
    | _ => pure ()
  return result

/-- A program can expose at most one raw signed self-entry contract. -/
def rawSelfEntry? (program : Program) : Except String (Option Ops.RawSelfEntry) := do
  let mut found : Option Ops.RawSelfEntry := none
  for method in program.methods do
    for entry in ← rawSelfEntriesIn method.ops do
      match found with
      | none => found := some entry
      | some expected =>
          unless expected == entry do
            throw "extract/unsupported: inconsistent raw self-entry tags or authority seeds"
  return found

private def lowerSlots (src : Core.IR.Program Ops.ValKind Ops.OpExt) : Array Slot := Id.run do
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

private def lowerVectors (src : Core.IR.Program Ops.ValKind Ops.OpExt)
    (slots : Array Slot) : Array Vector :=
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

private partial def scalarizeRawOp : Op → Op
  | .ite cmp lhs rhs thn els =>
      .ite cmp lhs rhs (thn.map scalarizeRawOp) (els.map scalarizeRawOp)
  | .forBody count body => .forBody count (body.map scalarizeRawOp)
  | .okState value => .returnU64 value
  | op => op

private def lowerMethod (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String Method := do
  let entry ← EntryAdapter.decode method.annotations method.paramCount method.paramWidths
    method.retCount method.paramTypes method.retTypes method.paramSchemas method.retSchema
  if entry.isGenerated then
    unless method.paramSchemas.isEmpty || method.paramSchemas.all schemaIsScalar do
      throw s!"extract/unsupported: svm generated aggregate parameter binding is not implemented for {method.ixName}"
  let ops ← ofSourceOps method.ops
  let (kind, ops) ←
    match entry with
    | .generated => pure (method.kind, ops)
    | .raw _ =>
        unless method.kind == .get || method.kind == .increment do
          throw s!"extract/unsupported: svm raw entry {method.ixName} must return bounded scalars"
        -- `Except Error (State × R)` is the source-level spelling for an effectful protocol
        -- handler, where R is one scalar or a bounded scalar product. Scalar success shorthands
        -- are normalized here; explicit tuple returns already use Core's generic return sequence.
        -- External account effects stay in place and no managed-State writeback is introduced.
        pure (.get, ops.map scalarizeRawOp)
  return {
    kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    paramTypes := method.paramTypes
    paramSchemas := method.paramSchemas
    retWidths := method.retWidths
    retTypes := method.retTypes
    retSchema := method.retSchema
    retCount := method.retCount
    entry
    ops
    evaluation := method.evaluation
  }

private partial def rawValUsesManagedState (paramCount : Nat) : Ops.Val → Bool
  | .arg index => paramCount ≤ index
  | .local _ | .lit _ | .loopIx => false
  | .field value _ | .bitNot value => rawValUsesManagedState paramCount value
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      rawValUsesManagedState paramCount lhs || rawValUsesManagedState paramCount rhs
  | .indexGet value _ index _ _ =>
      rawValUsesManagedState paramCount value || rawValUsesManagedState paramCount index
  | .select _ lhs rhs thn els =>
      rawValUsesManagedState paramCount lhs || rawValUsesManagedState paramCount rhs ||
        rawValUsesManagedState paramCount thn || rawValUsesManagedState paramCount els
  | .ext _ operands => operands.any (rawValUsesManagedState paramCount)

private partial def rawOpsUseManagedState (paramCount : Nat) (ops : Array Op) : Bool :=
  ops.any fun op =>
    let uses := rawValUsesManagedState paramCount
    match op with
    | .letLocal _ value | .setLocal _ value | .forAccum _ value _
    | .storeField _ value | .okState value | .returnU64 value | .returnState value => uses value
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs
    | .indexSet _ lhs rhs _ _ => uses lhs || uses rhs
    | .ite _ lhs rhs thn els =>
        uses lhs || uses rhs || rawOpsUseManagedState paramCount thn ||
          rawOpsUseManagedState paramCount els
    | .invoke _ _ data _ bump =>
        data.any (fun word => word.value?.any uses) || bump.any uses
    | .component call => call.values.any uses
    | .forBody _ body => rawOpsUseManagedState paramCount body
    | .joinLocal _ | .errorOverflow | .errorNamed _ => false

private def validateRawMethod (method : Method) : Except String Unit := do
  match method.entry with
  | .generated => pure ()
  | .raw _ =>
      unless method.kind == .get do
        throw s!"extract/unsupported: svm raw entry {method.ixName} must return bounded scalars"
      if hasStoreField method.ops || hasIndexSet method.ops ||
          rawOpsUseManagedState method.paramCount method.ops then
        throw s!"extract/unsupported: svm raw entry {method.ixName} must use external account storage, not managed State"

private def validateEntryDisjointness (methods : Array Method) : Except String Unit := do
  let generated := methods.filter (·.entry.isGenerated)
  for method in methods do
    match method.entry with
    | .generated => pure ()
    | .raw entry =>
        for candidate in generated do
          let generatedLen := 8 + 8 * candidate.paramCount
          if entry.minDataLen ≤ generatedLen && generatedLen ≤ entry.maxDataLen &&
              entry.tag == ABI.discFirstByte candidate.ixName candidate.paramCount then
            throw s!"extract/unsupported: svm raw entry {method.ixName} overlaps generated instruction {candidate.ixName}"

/-- Project the combined extractor dialect and lower it into an SVM-owned physical program. -/
def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  let source ← Core.Target.projectProgram extractRegistration src
  let slots := lowerSlots source
  let program : Program := {
    name := source.name
    slots
    vectors := lowerVectors source slots
    schema := source.schema
    methods := ← source.methods.mapM lowerMethod
  }
  EntryAdapter.validateUniqueTags (program.methods.map (·.entry))
  for method in program.methods do
    validateRawMethod method
  validateEntryDisjointness program.methods
  let _ ← rawSelfEntry? program
  return program

def Program.fields (p : Program) : Array String :=
  p.slots.map (·.name)

def fieldOffset (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.offset)

def fieldWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

private def inferredVector? (p : Program) (name : String) : Option Vector :=
  let prefix0 := name ++ "_0"
  let group := p.slots.filter fun slot =>
    slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
  if group.isEmpty then none
  else
    let digitPrefix (value : String) : String := Id.run do
      let mut result := ""
      for char in value.toList do
        if char.isDigit then result := result.push char else return result
      return result
    let length := p.slots.foldl (init := 0) fun current slot =>
      let rest :=
        if slot.name.startsWith (name ++ "_") then
          digitPrefix (slot.name.drop (name.length + 1) |>.copy)
        else ""
      match rest.toNat? with
      | some index => Nat.max current (index + 1)
      | none => current
    let stride := group.foldl (init := 0) fun width slot => width + slot.width
    let base := p.slots.find? fun slot =>
      slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
    if length == 0 || stride == 0 then none
    else base.map fun slot =>
      { name, baseOffset := slot.offset, length, strideBytes := stride }

private def vector? (p : Program) (name : String) : Option Vector :=
  match p.vectors.find? (·.name == name) with
  | some vector => some vector
  | none => inferredVector? p name

def vectorBaseOffset (p : Program) (name : String) : Option Nat :=
  (vector? p name).map (·.baseOffset)

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given
  else (vector? p name).map (·.length) |>.getD 0

def vectorStride (p : Program) (name : String) : Nat :=
  (vector? p name).map (·.strideBytes) |>.getD 8

/-- Width of the leaf at one byte offset within a source vector element. -/
def vectorLeafWidth (p : Program) (name : String) (byteOffset : Nat) : Option Nat := do
  let vector ← vector? p name
  if vector.leaves.isEmpty then
    -- Legacy fixtures only model vectors of UInt64 leaves.
    some 8
  else
    (vector.leaves.find? (·.offset == byteOffset)).map (·.width)

def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def isProgramShape (p : Program) : Bool :=
  p.methods.any (·.kind == .init) &&
    p.methods.any (·.kind == .increment) &&
    p.methods.any (·.kind == .get)

def usesCpi (p : Program) : Bool :=
  p.methods.any (hasInvoke ·.ops)

private partial def componentStackScratchEndIn (ops : Array Op) : Nat :=
  ops.foldl (init := Component.stackScratchEnd) fun current op =>
    match op with
    | .component call => Nat.max current call.stackScratchEnd
    | .ite _ _ _ thn els =>
        Nat.max current (Nat.max (componentStackScratchEndIn thn) (componentStackScratchEndIn els))
    | .forBody _ body => Nat.max current (componentStackScratchEndIn body)
    | _ => current

/-- Highest fixed stack cell required by any component used by this program. Keeping this
capability-driven preserves the established scalar-local layout for programs that do not use a
larger component. -/
def componentStackScratchEnd (p : Program) : Nat :=
  p.methods.foldl (init := Component.stackScratchEnd) fun current method =>
    Nat.max current (componentStackScratchEndIn method.ops)

def usesWalk (p : Program) : Bool :=
  usesCpi p || p.methods.any fun method => Ops.hasAcc1 (toSourceOps method.ops)

/-- True when any method selects an account through a bounded remaining-account view. Variable
remaining accounts move the real instruction-data and program-id location after the actual final
account, so the prelude must walk the runtime account count instead of the unrolled static prefix.
-/
def usesAccountView (p : Program) : Bool :=
  p.methods.any fun method => Ops.hasAccountView (toSourceOps method.ops)

private partial def highestInvokeIndex (ops : Array Op) : Nat :=
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

def methodAccountCount (method : Method) : Nat :=
  let highest := highestInvokeIndex method.ops
  -- CPI indices are relative to the external-account region; physical account 0 is state.
  let fromInvoke := if hasInvoke method.ops then Nat.max 3 (highest + 2) else 0
  let fromValues := Ops.opsMinAccounts (toSourceOps method.ops)
  Nat.max fromInvoke fromValues

private def inferredAccountCount (methods : Array Method) : Nat :=
  methods.foldl (init := 0) fun current method =>
    Nat.max current (methodAccountCount method)

def generatedAccountCount (p : Program) : Nat :=
  Nat.max 1 (inferredAccountCount (p.methods.filter (·.entry.isGenerated)))

def cpiAccountCount (p : Program) : Nat :=
  p.accountCountOverride.getD (inferredAccountCount p.methods)

def withAccountCount (p : Program) (accountCount : Nat) : Program :=
  { p with accountCountOverride := some accountCount }

private def sourceSlots (p : Program) : Array Core.IR.Slot :=
  p.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

def dataLen (p : Program) : Nat :=
  ABI.dataLenOf (sourceSlots p)

def inputLayout (p : Program) : ABI.InputLayout :=
  ABI.inputLayoutOf (dataLen p) (usesWalk p) (cpiAccountCount p)

def layoutMarkerHex (p : Program) : Except String String :=
  ABI.layoutMarkerHexOf (sourceSlots p)

private def kindTag : Core.IR.MethodKind → String
  | .init => "init"
  | .increment => "mut"
  | .get => "view"

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

/-- Preserve the old closed-union spelling in canonical digests during the IR migration. -/
private def legacyCmpRepr (cmp : Ops.Cmp) : String :=
  "ProofForge.Ops.Cmp." ++ cmpTag cmp

private def pdaSeedCanon : Ops.PdaSeed → String
  | .ascii value => s!"s.{value}"
  | .stateKey => "state"
  | .accKey i => s!"k.{i}"
  | .accData i offset length => s!"d.{i}.{offset}.{length}"

private partial def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field base name => s!"f.{name}({valCanon base})"
  | .ext .clockSlot #[] => "clk"
  | .ext .clockEpoch #[] => "epo"
  | .ext .unixTime #[] => "unix"
  | .ext .slotsPerEpoch #[] => "spe"
  | .ext .signerKey0 #[] => "k0"
  | .ext .accLamports0 #[] => "lp0"
  | .ext .accOwner0 #[] => "ow0"
  | .ext .accDataLen0 #[] => "dl0"
  | .ext .accN #[] => "nacc"
  | .ext .isSigner0 #[] => "sg0"
  | .ext .isWritable0 #[] => "wr0"
  | .ext .isExecutable0 #[] => "ex0"
  | .ext .accLamports1 #[] => "lp1"
  | .ext .accOwner1 #[] => "ow1"
  | .ext .accDataLen1 #[] => "dl1"
  | .ext .isSigner1 #[] => "sg1"
  | .ext .isWritable1 #[] => "wr1"
  | .ext .isExecutable1 #[] => "ex1"
  | .ext (.findPda seed) #[] => s!"pda.{seed}"
  | .ext (.checkPda seed) #[bump] => s!"chk.{seed}:{valCanon bump}"
  | .ext (.rentExemption len) #[] => s!"rent.{len.toNat}"
  | .ext .cpiReturn #[] => "cret"
  | .ext (.sha256Lit seed) #[] => s!"sha.{seed}"
  | .ext (.keccak256Lit seed) #[] => s!"kec.{seed}"
  | .ext .byteSwap64 #[word] => s!"bswap64({valCanon word})"
  | .ext (.accKeyWord acc word) #[] => s!"kw.{acc}.{word}"
  | .ext (.accOwnerWord acc word) #[] => s!"ow.{acc}.{word}"
  | .ext (.accDataWord acc word) #[] => s!"dw.{acc}.{word}"
  | .ext (.component query) operands => query.canonical valCanon operands
  | .ext (.accLamportsN acc) #[] => s!"lpN.{acc}"
  | .ext (.accDataLenN acc) #[] => s!"dlN.{acc}"
  | .ext (.isSignerN acc) #[] => s!"sgN.{acc}"
  | .ext (.isWritableN acc) #[] => s!"wrN.{acc}"
  | .ext (.isExecutableN acc) #[] => s!"exN.{acc}"
  | .ext (.signerKeyN acc) #[] => s!"sk.{acc}"
  | .ext (.ownerIsSelf acc) #[] => s!"ois.{acc}"
  | .ext (.findPdaSeeds seeds) #[] =>
      s!"pdas.[{String.intercalate "," (seeds.toList.map pdaSeedCanon)}]"
  | .ext (.checkPdaSeeds account seeds) #[] =>
      s!"chkpdas.{account}.[{String.intercalate "," (seeds.toList.map pdaSeedCanon)}]"
  | .bitAnd lhs rhs => s!"and({valCanon lhs},{valCanon rhs})"
  | .bitOr lhs rhs => s!"or({valCanon lhs},{valCanon rhs})"
  | .bitXor lhs rhs => s!"xor({valCanon lhs},{valCanon rhs})"
  | .bitNot value => s!"not({valCanon value})"
  | .shiftL lhs rhs => s!"shl({valCanon lhs},{valCanon rhs})"
  | .shiftR lhs rhs => s!"shr({valCanon lhs},{valCanon rhs})"
  | .indexGet base name index len offset =>
      if offset == 0 then s!"idx.{name}[{valCanon index}/{len}]({valCanon base})"
      else s!"idx.{name}+{offset}[{valCanon index}/{len}]({valCanon base})"
  | .loopIx => "ix"
  | .select cmp lhs rhs thn els =>
      s!"sel.{legacyCmpRepr cmp}({valCanon lhs},{valCanon rhs},{valCanon thn},{valCanon els})"
  | .addU64 lhs rhs => s!"uadd({valCanon lhs},{valCanon rhs})"
  | .subU64 lhs rhs => s!"usub({valCanon lhs},{valCanon rhs})"
  | .mulU64 lhs rhs => s!"umul({valCanon lhs},{valCanon rhs})"
  | .divU64 lhs rhs => s!"udiv({valCanon lhs},{valCanon rhs})"
  | .modU64 lhs rhs => s!"umod({valCanon lhs},{valCanon rhs})"
  | .ext kind operands =>
      s!"ext.{repr kind}({String.intercalate "," (operands.map valCanon).toList})"

private partial def opsCanon (ops : Array Op) : String :=
  let one (op : Op) : String :=
    match op with
    | .letLocal i value => s!"let.{i}({valCanon value})"
    | .joinLocal i => s!"join.{i}"
    | .setLocal i value => s!"set.{i}({valCanon value})"
    | .checkedAddU64 lhs rhs => s!"add({valCanon lhs},{valCanon rhs})"
    | .checkedSubU64 lhs rhs => s!"sub({valCanon lhs},{valCanon rhs})"
    | .checkedMulU64 lhs rhs => s!"mul({valCanon lhs},{valCanon rhs})"
    | .checkedDivU64 lhs rhs => s!"div({valCanon lhs},{valCanon rhs})"
    | .checkedModU64 lhs rhs => s!"mod({valCanon lhs},{valCanon rhs})"
    | .ite cmp lhs rhs thn els =>
        s!"ite.{cmpTag cmp}({valCanon lhs},{valCanon rhs},[{opsCanon thn}],[{opsCanon els}])"
    | .invoke programIx metas data seeds bump =>
        let metaCanon := String.intercalate "," <| metas.toList.map fun entry =>
          let dataLen :=
            match entry.expectedDataLen with
            | some n => s!"@{n}"
            | none => ""
          let policy :=
            match entry.accountData with
            | some (.token2022Base .mint) => "~t22mint"
            | some (.token2022Base .account) => "~t22acct"
            | none => ""
          s!"{entry.acc}{if entry.signer then "s" else ""}{if entry.writable then "w" else ""}{dataLen}{policy}"
        let wordCanon (word : Ops.CpiWord Ops.Val) : String :=
          match word with
          | .u8le (.lit n) => s!"u8.{n.toNat}"
          | .u8le value => s!"u8v.{valCanon value}"
          | .u16le value => s!"u16.{valCanon value}"
          | .u32le (.lit n) => s!"u32.{n.toNat}"
          | .u32le value => s!"u32v.{valCanon value}"
          | .u64le value => s!"u64.{valCanon value}"
          | .selfEntry tag authoritySeed => s!"self.{tag.toNat}.{authoritySeed}"
          | .ascii value => s!"s.{value}"
          | .programId => "pid"
          | .accKey i => s!"k.{i}"
        let dataCanon := String.intercalate "," (data.toList.map wordCanon)
        let signer :=
          match seeds.toList, bump with
          -- Preserve the v1 spelling, and therefore existing fixture digests, for the original
          -- one-ASCII-seed signer shape.
          | [.ascii value], some valueBump => s!",s.{value}:{valCanon valueBump}"
          | _, some valueBump =>
              let seedCanon := String.intercalate "," (seeds.toList.map pdaSeedCanon)
              s!",s.[{seedCanon}]:{valCanon valueBump}"
          | _, none => ""
        s!"inv({programIx},[{metaCanon}],[{dataCanon}]{signer})"
    | .component call => call.canonical valCanon
    | .forAccum n addend resultLocal =>
        s!"for.{resultLocal}({n},{valCanon addend})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet name index value len offset =>
        if offset == 0 then s!"iset.{name}[{valCanon index}/{len}]({valCanon value})"
        else s!"iset.{name}+{offset}[{valCanon index}/{len}]({valCanon value})"
    | .storeField name value => s!"st.{name}({valCanon value})"
    | .okState value => s!"ok({valCanon value})"
    | .errorOverflow => "ovf"
    | .errorNamed name => s!"err.{name}"
    | .returnU64 value => s!"retu({valCanon value})"
    | .returnState value => s!"rets({valCanon value})"
  String.intercalate ";" (ops.toList.map one)

/-- Stable source identity, computed from SVM-owned Ops without rebuilding the mixed legacy IR. -/
def canonical (p : Program) : String :=
  let fields := String.intercalate "," p.fields.toList
  let methods :=
    (p.methods.qsort (fun lhs rhs => lhs.ixName < rhs.ixName)).toList.map fun method =>
      let base :=
        s!"{kindTag method.kind}:{method.ixName}:{method.paramCount}:[{opsCanon method.ops}]"
      let base :=
        if (method.paramWidths.isEmpty || method.paramWidths.all (· == 8)) && method.retCount == 1 then
          base
        else
          let widths := String.intercalate "," (method.paramWidths.map toString).toList
          s!"{kindTag method.kind}:{method.ixName}:{method.paramCount}:{widths}:r{method.retCount}:[{opsCanon method.ops}]"
      match method.entry with
      | .generated => base
      | .raw entry => s!"{base}:{entry.canonical}"
  s!"{p.name}|{fields}|{String.intercalate "/" methods}"

def digestHex (p : Program) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical p))

def discHex (m : Method) : Except String String :=
  ABI.discHexOf m.ixName m.paramCount

def lastName := Core.IR.lastName
def ixNameOfLean := Core.IR.ixNameOfLean
def u64Hex := Core.IR.u64Hex

end ProofForge.Svm.IR
