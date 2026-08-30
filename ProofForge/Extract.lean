import Lean
import ProofForge.Extract.Ops
import ProofForge.Profile
import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Svm.Runtime
import ProofForge.Evm.Runtime
import ProofForge.Evm.Codec
import ProofForge.Wasm.Xrpl.Runtime
import ProofForge.Extract.Lexical
import ProofForge.Extract.Decode

open Lean

namespace ProofForge.Extract

def decodeBody (env : Environment) (e : Expr) (preserveLocals : Bool := false)
    (stateType? : Option Name := none) :
    Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  -- Canonicalize syntax-only aliases around control flow before shape decoding.
  -- A method with structured-State sequencing also retains adjacent scalar lets so `decodeExpr`
  -- can materialize bounded lookups instead of duplicating them through every later projection.
  -- Account effects need the same lexical boundary: a value captured before a write or CPI must
  -- not be substituted into that later effect and re-read after the mutation.
  let hasStructuredState := containsStructuredStateLet env 128 body
  let hasSequencedSvmEffects := mentionsSvmEffect env 128 body
  let hasSequencedNearEffects := mentionsNearEffect env 128 body
  let retainLets := hasStructuredState || hasSequencedSvmEffects || hasSequencedNearEffects
  let fullySubstituted := if retainLets then body else substLets 256 body
  let body :=
    if (unfoldUserHelper env fullySubstituted).isSome then fullySubstituted
    else if retainLets then body else zetaPureHeadLets env 32 body
  let body := if retainLets then body else substIteLets 256 body
  decodeExpr env 128 body (preserveLocals := preserveLocals || hasSequencedSvmEffects)
    (stateType? := stateType?)

private def writesOptionLeaf (fuel : Nat) (ops : Array Ops.Op) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun
      | .okState (.field _ n) => n.endsWith "_tag" || n.endsWith "_p0"
      | .okState (.lit _) => true
      | .okState (.arg _) => true
      | .storeField n _ => n.endsWith "_tag" || n.endsWith "_p0"
      | .ite _ _ _ t f => writesOptionLeaf fuel' t || writesOptionLeaf fuel' f
      | _ => false

private def hasIte (ops : Array Ops.Op) : Bool :=
  ops.any fun | .ite .. => true | _ => false

/-- 可变入口必须有 checked 算术、Option 双叶，或比较 ite（窄宽上界）。 -/
def decodeMutating (env : Environment) (e : Expr) (stateType? : Option Name := none) :
    Except String (Array Ops.Op) := do
  let ops ← decodeBody env e true stateType?
  if Ops.hasCheckedArith ops || writesOptionLeaf 8 ops || hasIte ops ||
      Ops.hasInvoke ops || Ops.hasEvmEffect ops || Ops.hasNearEffect ops || Ops.hasLangOp ops ||
        Ops.hasForAccum ops || Ops.hasIndexSet ops || Ops.hasStoreField ops then
    return ops
  else
    throw "extract/unsupported: mutating method missing checked arith"

private def codecScalarOfType (e : Expr) : Option Core.Codec.Scalar :=
  match e.consumeMData.getAppFn.constName? with
  | some ``Bool => some .boolean
  | some ``UInt8 => some .uint8
  | some ``UInt16 => some .uint16
  | some ``UInt32 => some .uint32
  | some ``UInt64 => some .uint64
  | some n =>
      if n == addr20Name then some .address20
      else if n == uint128Name then some .uint128
      else if n == uint256Name || n == evmUInt256AliasName then some .uint256
      else if n == fixedBytesName || n == evmBytes32AliasName then
        (fixedBytesSize? e).map (.fixedBytes ·)
      else none
  | none => none

private def legacyWidthOfScalar : Core.Codec.Scalar → Nat
  | type =>
      match Evm.Codec.legacyWidthOfScalar type with
      | .ok width => width
      | .error _ => type.byteWidth

private def widthOfType (e : Expr) : Option Nat :=
  (codecScalarOfType e).map legacyWidthOfScalar

/-- Derive a bounded logical codec shape without choosing Borsh, ABI, account, or storage layout. -/
private partial def codecSchemaOfTypeAt (env : Environment) (fuel : Nat)
    (ancestors : Array Name) (type : Expr) : Except String Core.Codec.Schema := do
  if fuel == 0 then
    throw "extract/unsupported: boundary schema nesting exceeds extractor limit"
  let type := type.consumeMData
  if let some scalar := codecScalarOfType type then
    return .scalar scalar
  let head := type.getAppFn.constName?
  if head == some ``Unit || head == some ``PUnit then
    return .unit
  let args := type.getAppArgs
  if head == some ``Prod then
    unless args.size ≥ 2 do
      throw "extract/unsupported: malformed Prod boundary type"
    return .tuple #[
      ← codecSchemaOfTypeAt env (fuel - 1) ancestors args[args.size - 2]!,
      ← codecSchemaOfTypeAt env (fuel - 1) ancestors args[args.size - 1]!
    ]
  if head == some ``Option then
    let some payload := args.back?
      | throw "extract/unsupported: malformed Option boundary type"
    return .option (← codecSchemaOfTypeAt env (fuel - 1) ancestors payload)
  if head == some ``Vector then
    unless args.size ≥ 2 do
      throw "extract/unsupported: malformed Vector boundary type"
    let some length := natLiteral? args[args.size - 1]!
      | throw "extract/unsupported: Vector boundary length is not a literal"
    let element ← codecSchemaOfTypeAt env (fuel - 1) ancestors args[args.size - 2]!
    return .fixedArray length element
  if head == some boundedVecName then
    unless args.size ≥ 2 do
      throw "extract/unsupported: malformed BoundedVec boundary type"
    let some capacity := natLiteral? args[args.size - 1]!
      | throw "extract/unsupported: BoundedVec boundary capacity is not a literal"
    let element ← codecSchemaOfTypeAt env (fuel - 1) ancestors args[args.size - 2]!
    return .boundedArray capacity element
  if head == some boundedBytesName || head == some boundedStringName then
    let some capacityExpr := args.back?
      | throw "extract/unsupported: malformed bounded byte boundary type"
    let some capacity := natLiteral? capacityExpr
      | throw "extract/unsupported: bounded byte capacity is not a literal"
    return if head == some boundedBytesName then .boundedBytes capacity else .boundedString capacity
  if head == some ``Array then
    throw "extract/unsupported: Array boundary is dynamic; use Vector or BoundedVec"
  if head == some fixedBytesName then
    throw "extract/unsupported: FixedBytes boundary size must be a literal in 1..32"
  let some typeName := head
    | throw "extract/unsupported: polymorphic boundary type"
  unless isUserType env typeName || Attr.isBoundary env typeName do
    throw s!"extract/unsupported: unsupported boundary type {typeName}"
  if ancestors.contains typeName then
    throw s!"extract/unsupported: recursive boundary type {typeName}"
  let some (.inductInfo info) := env.find? typeName
    | throw s!"extract/unsupported: malformed boundary type {typeName}"
  if info.numParams != 0 || info.numIndices != 0 || !args.isEmpty then
    throw s!"extract/unsupported: polymorphic boundary type {typeName}"
  if info.isRec then
    throw s!"extract/unsupported: recursive boundary type {typeName}"
  if info.ctors.isEmpty then
    throw s!"extract/unsupported: empty boundary type {typeName}"
  let ancestors := ancestors.push typeName
  if isStructure env typeName then
    unless (getStructureParentInfo env typeName).isEmpty do
      throw s!"extract/unsupported: boundary record {typeName} uses inheritance"
    let fields := getStructureFields env typeName
    if fields.isEmpty then
      throw s!"extract/unsupported: boundary record {typeName} has no fields"
    let mut schemas : Array (String × Core.Codec.Schema) := #[]
    for field in fields do
      if (isSubobjectField? env typeName field).isSome then
        throw s!"extract/unsupported: boundary record {typeName} uses inheritance"
      let some fieldType := fieldTypeExpr env typeName field
        | throw s!"extract/unsupported: boundary field {typeName}.{field} has no type"
      schemas := schemas.push (field.toString,
        ← codecSchemaOfTypeAt env (fuel - 1) ancestors fieldType)
    return .record typeName.toString schemas
  let mut variants : Array (String × Core.Codec.Schema) := #[]
  for ctorName in info.ctors do
    let some (.ctorInfo ctor) := env.find? ctorName
      | throw s!"extract/unsupported: malformed boundary constructor {ctorName}"
    let mut payload : Array Core.Codec.Schema := #[]
    for index in [:ctor.numFields] do
      let some fieldType := forallDomainAt? 32 index ctor.type
        | throw s!"extract/unsupported: boundary constructor {ctorName} has no field type"
      payload := payload.push (← codecSchemaOfTypeAt env (fuel - 1) ancestors fieldType)
    let payloadSchema :=
      match payload.toList with
      | [] => .unit
      | [schema] => schema
      | _ => .tuple payload
    variants := variants.push (Core.IR.lastName ctorName.toString, payloadSchema)
  return .enumeration typeName.toString 8 variants

def codecSchemaOfType (env : Environment) (type : Expr) :
    Except String Core.Codec.Schema := do
  let schema ← codecSchemaOfTypeAt env 32 #[] type
  match Core.Codec.validate schema with
  | .ok _ => return schema
  | .error reason => throw s!"extract/unsupported: {reason}"

/-- User parameter domains. init includes every binder; mutate/view drop persisted State. -/
private def inferParamTypeExprs (e : Expr) (kind : Core.IR.MethodKind) : Array Expr :=
  let rec collect (fuel : Nat) (e : Expr) (acc : Array Expr) : Array Expr :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      match strip e with
      | .lam _ type body _ => collect fuel' body (acc.push type)
      | .letE _ _ _ body _ => collect fuel' body acc
      | _ => acc
  let types := collect 32 e #[]
  match kind with
  | .init => types
  | .increment | .get => if types.isEmpty then #[] else types.extract 1 types.size

private def inferParamSchemas (env : Environment) (e : Expr) (kind : Core.IR.MethodKind) :
    Except String (Array Core.Codec.Schema) :=
  (inferParamTypeExprs e kind).mapM (codecSchemaOfType env)

/-- Scalar compatibility metadata is complete or absent; aggregates never masquerade as u64. -/
private def scalarTypesOfSchemas (schemas : Array Core.Codec.Schema) :
    Array Core.Codec.Scalar := Id.run do
  let mut types := #[]
  for schema in schemas do
    match schema with
    | .scalar type => types := types.push type
    | _ => return #[]
  return types

private def logicalReturnSchema (env : Environment) (kind : Core.IR.MethodKind) (type : Expr) :
    Except String Core.Codec.Schema := do
  match kind with
  | .init => return .unit
  | .get => return ← codecSchemaOfType env type
  | .increment =>
      let args := type.consumeMData.getAppArgs
      unless type.consumeMData.getAppFn.constName? == some ``Except && args.size ≥ 2 do
        throw "extract/unsupported: mutating boundary must return Except Error (State × Result)"
      let success := args[args.size - 1]!.consumeMData
      let successArgs := success.getAppArgs
      unless success.getAppFn.constName? == some ``Prod && successArgs.size ≥ 2 do
        throw "extract/unsupported: mutating boundary must return Except Error (State × Result)"
      return ← codecSchemaOfType env successArgs[successArgs.size - 1]!

/-- Expand a top-level bounded result into its fixed scalar frame before either target chooses an
output wire format. This is source projection only: Borsh/ABI length and padding remain target
owned. Richer element shapes stay closed until recursive result projection is qualified. -/
private def expandBoundedReturnOps (schema : Core.Codec.Schema) (ops : Array Ops.Op) :
    Except String (Array Ops.Op) :=
  match ops.toList, schema with
  | [.returnU64 root], .boundedArray capacity (.scalar type)
  | [.returnState root], .boundedArray capacity (.scalar type) => do
      unless Core.Codec.Scalar.isWellFormed type && Core.Codec.Scalar.byteWidth type ≤ 8 do
        throw "extract/unsupported: bounded result currently requires one-limb scalar elements"
      let mut result : Array Ops.Op := #[.returnU64 (.field root "length")]
      for i in [0:capacity] do
        result := result.push (.returnU64 (.indexGet root "values" (.lit (UInt64.ofNat i)) capacity 0))
      pure result
  | [.returnU64 root], .boundedBytes capacity | [.returnU64 root], .boundedString capacity
  | [.returnState root], .boundedBytes capacity | [.returnState root], .boundedString capacity => do
      let mut result : Array Ops.Op := #[.returnU64 (.field root "length")]
      for i in [0:capacity] do
        result := result.push (.returnU64 (.indexGet root "values" (.lit (UInt64.ofNat i)) capacity 0))
      pure result
  | leaves, .boundedArray capacity (.scalar type) => do
      unless Core.Codec.Scalar.isWellFormed type && Core.Codec.Scalar.byteWidth type ≤ 8 do
        throw "extract/unsupported: bounded result currently requires one-limb scalar elements"
      unless leaves.length == capacity + 1 do
        throw "extract/unsupported: constructed bounded result has the wrong fixed-frame size"
      leaves.toArray.mapM fun
        | .returnU64 value | .returnState value => pure (.returnU64 value)
        | _ => throw "extract/unsupported: constructed bounded result must contain scalar leaves"
  | leaves, .boundedBytes capacity | leaves, .boundedString capacity => do
      unless leaves.length == capacity + 1 do
        throw "extract/unsupported: constructed bounded result has the wrong fixed-frame size"
      leaves.toArray.mapM fun
        | .returnU64 value | .returnState value => pure (.returnU64 value)
        | _ => throw "extract/unsupported: constructed bounded result must contain scalar leaves"
  | _, .boundedArray .. =>
      throw "extract/unsupported: bounded result requires scalar elements"
  | _, _ => pure ops

/-- Count the fixed UInt64 payload lanes in the source representation of one enum constructor.
The shared frame deliberately follows the representation Extract already uses for tagged inputs;
Borsh and ABI tag widths, active-lane rules, and wire encoding remain target-owned. -/
private def enumReturnPayloadWords : Core.Codec.Schema → Except String Nat
  | .unit => pure 0
  | .scalar (.uint 64) => pure 1
  | .tuple items => do
      for item in items do
        unless item == .scalar .uint64 do
          throw "extract/unsupported: tagged enum result fields must be UInt64"
      pure items.size
  | _ => throw "extract/unsupported: tagged enum result fields must be UInt64"

/-- Verify that control-owning construction preserved an exact logical result frame on every
successful path. Error exits are intentionally frame-free; nearby locals are never inferred as
missing leaves. -/
private def validateConstructedReturnFrame (ops : Array Ops.Op) (expected : Nat) :
    Except String Unit := do
  let graph ← IR.toCFG ops
  let mut sawSuccess := false
  for block in graph.blocks do
    match block.terminator with
    | .exit (.returnU64 _) =>
        sawSuccess := true
        unless expected == 1 do
          throw s!"extract/unsupported: constructed result block {block.id} returns 1 of {expected} leaves"
    | .exit (.returnU64s values) =>
        sawSuccess := true
        unless values.size == expected do
          throw s!"extract/unsupported: constructed result returns {values.size} of {expected} leaves"
    | .exit (.returnState _) | .exit (.okState _) | .exit (.initialize _) =>
        throw "extract/unsupported: constructed result lost its explicit fixed frame"
    | _ => pure ()
  unless sawSuccess do
    throw "extract/unsupported: constructed result has no successful fixed frame"

/-- Project a top-level tagged result into a fixed source frame before either target selects its
wire policy. Option uses `slot_tag, slot_p0`; enums use `variant_tag, variant_p0, ...`, matching the
existing input-side source names without importing Borsh or ABI geometry into shared extraction. -/
private def expandTaggedReturnOps (schema : Core.Codec.Schema) (ops : Array Ops.Op) :
    Except String (Array Ops.Op) := do
  let root? := match ops.toList with
    | [.returnU64 root] | [.returnState root] => some root
    | _ => none
  match schema, root? with
  | .option (.scalar type), some root =>
      unless Core.Codec.Scalar.isWellFormed type && Core.Codec.Scalar.byteWidth type ≤ 8 do
        throw "extract/unsupported: tagged Option result currently requires a one-limb scalar payload"
      pure #[
        .returnU64 (.field root "slot_tag"),
        .returnU64 (.field root "slot_p0")
      ]
  | .option _, some _ =>
      throw "extract/unsupported: tagged Option result currently requires a one-limb scalar payload"
  | .option (.scalar type), none => do
      unless Core.Codec.Scalar.isWellFormed type && Core.Codec.Scalar.byteWidth type ≤ 8 do
        throw "extract/unsupported: tagged Option result currently requires a one-limb scalar payload"
      validateConstructedReturnFrame ops 2
      pure ops
  | .option _, none =>
      throw "extract/unsupported: tagged Option result currently requires a one-limb scalar payload"
  | .enumeration _ tagBits variants, some root => do
      unless tagBits == 8 && !variants.isEmpty && variants.size ≤ 256 do
        throw "extract/unsupported: tagged enum result requires a nonempty u8 tag space"
      let counts ← variants.mapM fun variant => enumReturnPayloadWords variant.2
      let payloadWords := counts.foldl (init := 0) max
      let mut result : Array Ops.Op := #[.returnU64 (.field root "variant_tag")]
      for i in [0:payloadWords] do
        result := result.push (.returnU64 (.field root ("variant_p" ++ toString i)))
      pure result
  | .enumeration .., none =>
      throw "extract/unsupported: constructed tagged results are not yet represented as a fixed source frame"
  | _, _ => pure ops

/-- Project a compiler-owned static record result into the same fixed scalar frame already used
for ordinary source records and wide scalars. The shared layer owns only logical field paths and
little fixed limbs; Borsh/ABI widths, offsets, padding, and publication remain target-owned. -/
private def expandStaticRecordReturnOps (schema : Core.Codec.Schema) (ops : Array Ops.Op) :
    Except String (Array Ops.Op) := do
  let .record _ _ := schema | return ops
  let root? := match ops.toList with
    | [.returnU64 root] | [.returnState root] => some root
    | _ => none
  let some root := root? | return ops
  let leaves ← Core.Codec.staticLeaves schema
  let mut result : Array Ops.Op := #[]
  for leaf in leaves do
    let width := leaf.type.byteWidth
    unless leaf.type.isWellFormed && 0 < width && width ≤ 32 do
      throw "extract/unsupported: static record return has malformed scalar leaf"
    let parts := (width + 7) / 8
    let name := leaf.sourceName
    if parts == 1 then
      result := result.push (.returnU64 (.field root name))
    else
      for part in [0:parts] do
        result := result.push (.returnU64 (.field root s!"{name}_w{part}"))
  return result

private def markMethodArgs (kind : Core.IR.MethodKind) (count : Nat) (body : Expr) : Expr :=
  let marker (index : Nat) := mkApp (mkConst ``methodArgRef) (mkNatLit index)
  let abiIndex (dbIndex : Nat) : Nat :=
    match kind with
    | .init => count - 1 - dbIndex
    | .increment | .get =>
      if dbIndex + 1 == count then count - 1 else count - 2 - dbIndex
  let rec go (depth : Nat) (e : Expr) : Expr :=
    match e with
    | .bvar index =>
      if depth ≤ index && index - depth < count then marker (abiIndex (index - depth)) else e
    | .app fn arg => .app (go depth fn) (go depth arg)
    | .lam name type body info => .lam name (go depth type) (go (depth + 1) body) info
    | .forallE name type body info => .forallE name (go depth type) (go (depth + 1) body) info
    | .letE name type value body nondep =>
      .letE name (go depth type) (go depth value) (go (depth + 1) body) nondep
    | .mdata data body => .mdata data (go depth body)
    | .proj type index value => .proj type index (go depth value)
    | e => e
  go 0 body

def extractMethod (env : Environment) (kind : Core.IR.MethodKind) (n : Name) :
    Except String IR.Method := do
  let some info := env.find? n
    | throw s!"extract/unsupported: unknown {n}"
  let some e := info.value?
    | throw s!"extract/unsupported: no value {n}"
  let sketch := sketchOfExpr e
  let stateType? :=
    match kind, strip e with
    | .init, _ => none
    | _, .lam _ type _ _ => type.consumeMData.getAppFn.constName?
    | _, _ => none
  let (nLams, sourceBody) := peelLams e
  let sourceBody := markMethodArgs kind nLams sourceBody
  let ops0 ←
    match kind with
    | .increment => decodeMutating env sourceBody stateType?
    | _ => decodeBody env sourceBody (stateType? := stateType?)
  let lean := Core.IR.lastName n.toString
  -- Inline entry helpers can own the source loop, so the entry body itself need not expose
  -- `ForIn.forIn`. Explicit stores in the decoded loop distinguish state-carrying loops from
  -- accumulator/early-return loops and are the authoritative post-inline signal.
  let rec hasStateLoop (fuel : Nat) (ops : Array Ops.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      ops.any fun
        | .forBody _ body =>
            Ops.hasStoreField body || Ops.hasIndexSet body || hasStateLoop fuel' body
        | .ite _ _ _ thn els => hasStateLoop fuel' thn || hasStateLoop fuel' els
        | _ => false
  let stateLoop := hasStateLoop 16 ops0
  let rec capturedStateArg (fuel : Nat) (v : Ops.Val) : Nat :=
    match fuel with
    | 0 => 0
    | fuel' + 1 =>
      let max2 l r := max (capturedStateArg fuel' l) (capturedStateArg fuel' r)
      match v with
      | .field (.arg i) _ => i
      | .field base _ | .bitNot base | .checkPda _ base => capturedStateArg fuel' base
      | .indexGet base _ index _ _ => max2 base index
      | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
      | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
      | .mapGetU64 l r => max2 l r
      | .select _ l r t f => max (max2 l r) (max2 t f)
      | _ => 0
  let normalizeStateLoopVal (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    let expectedStateArg := nLams + 1
    let captured := capturedStateArg fuel v
    let binderShift := if captured > expectedStateArg then captured - expectedStateArg else 0
    let rec go (fuel : Nat) (v : Ops.Val) : Ops.Val :=
      match fuel with
      | 0 => v
      | fuel' + 1 =>
        let state := .arg (nLams - 1)
        match v with
        -- Loop body binders are accumulator 0 and index 1. A dependent branch can insert
        -- additional proof binders; a captured source-state projection witnesses that shift.
        | .arg i =>
            let i := if i ≥ binderShift then i - binderShift else i
            if i ≥ 2 then .arg (i - 2) else .arg i
        | .field _ name => .field state name
        | .indexGet _ name index len off => .indexGet state name (go fuel' index) len off
        | .checkPda seed bump => .checkPda seed (go fuel' bump)
        | .bitAnd l r => .bitAnd (go fuel' l) (go fuel' r)
        | .bitOr l r => .bitOr (go fuel' l) (go fuel' r)
        | .bitXor l r => .bitXor (go fuel' l) (go fuel' r)
        | .bitNot x => .bitNot (go fuel' x)
        | .shiftL l r => .shiftL (go fuel' l) (go fuel' r)
        | .shiftR l r => .shiftR (go fuel' l) (go fuel' r)
        | .select c l r t f => .select c (go fuel' l) (go fuel' r) (go fuel' t) (go fuel' f)
        | .addU64 l r => .addU64 (go fuel' l) (go fuel' r)
        | .subU64 l r => .subU64 (go fuel' l) (go fuel' r)
        | .mulU64 l r => .mulU64 (go fuel' l) (go fuel' r)
        | .divU64 l r => .divU64 (go fuel' l) (go fuel' r)
        | .modU64 l r => .modU64 (go fuel' l) (go fuel' r)
        | v => v
    go fuel v
  let rec normalizeStateLoopOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      let nv := normalizeStateLoopVal fuel'
      match op with
      | .letLocal i v => .letLocal i (nv v)
      | .joinLocal i => .joinLocal i
      | .setLocal i v => .setLocal i (nv v)
      | .checkedAddU64 l r => .checkedAddU64 (nv l) (nv r)
      | .checkedSubU64 l r => .checkedSubU64 (nv l) (nv r)
      | .checkedMulU64 l r => .checkedMulU64 (nv l) (nv r)
      | .checkedDivU64 l r => .checkedDivU64 (nv l) (nv r)
      | .checkedModU64 l r => .checkedModU64 (nv l) (nv r)
      | .ite cmp l r t f =>
          .ite cmp (nv l) (nv r) (t.map (normalizeStateLoopOp fuel'))
            (f.map (normalizeStateLoopOp fuel'))
      | .invoke prog metas data seed bump =>
          .invoke prog metas (data.map (·.map nv)) seed (bump.map nv)
      | .forAccum bound addend resultLocal => .forAccum bound (nv addend) resultLocal
      | .forBody bound body => .forBody bound (body.map (normalizeStateLoopOp fuel'))
      | .indexSetLeaf name index value len leaf =>
          .indexSetLeaf name (nv index) (nv value) len leaf
      | .indexSet name index value len off => .indexSet name (nv index) (nv value) len off
      | .storeField name value => .storeField name (nv value)
      | .okState value => .okState (nv value)
      | .returnU64 value => .returnU64 (nv value)
      | .returnState value => .returnState (nv value)
      | op => op
  let ops0 := if stateLoop then ops0.map (normalizeStateLoopOp 32) else ops0
  -- Resolve entry-parameter markers only after nested callback binders have been normalized.
  let rec flipVal (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      match v with
      | .arg _ => v
      | .local i =>
        if methodArgLocalBase ≤ i then .arg (i - methodArgLocalBase) else v
      | .field b n => .field (flipVal fuel' b) n
      | .lit _ => v
      | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
      | .accN | .isSigner0 | .isWritable0 | .isExecutable0
      | .accLamports1 | .accOwner1 | .accDataLen1
      | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
      | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
      | .accKeyWord _ _ | .accOwnerWord _ _ | .accDataWord _ _
      | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
      | .signerKeyN _ | .ownerIsSelf _ | .findPdaSeeds _ | .checkPdaSeeds _ _
      | .nearBlockIndex | .nearBlockTimestamp | .nearPredecessor
      | .nearAttachedDeposit | .nearAccountBalance | .nearCurrentAccountId => v
      | .byteSwap64 word => .byteSwap64 (flipVal fuel' word)
      | .accDataWordAt a b s c i => .accDataWordAt a b s c (flipVal fuel' i)
      | .ext (.svm (.component query)) operands =>
          .ext (.svm (.component query)) (operands.map (flipVal fuel'))
      | .checkPda s b => .checkPda s (flipVal fuel' b)
      | .bitAnd l r => .bitAnd (flipVal fuel' l) (flipVal fuel' r)
      | .bitOr l r => .bitOr (flipVal fuel' l) (flipVal fuel' r)
      | .bitXor l r => .bitXor (flipVal fuel' l) (flipVal fuel' r)
      | .bitNot v => .bitNot (flipVal fuel' v)
      | .shiftL l r => .shiftL (flipVal fuel' l) (flipVal fuel' r)
      | .shiftR l r => .shiftR (flipVal fuel' l) (flipVal fuel' r)
      | .indexGet b n i k off =>
          .indexGet (flipVal fuel' b) n (flipVal fuel' i) k off
      | .loopIx => v
      | .select c l r t f =>
          .select c (flipVal fuel' l) (flipVal fuel' r) (flipVal fuel' t) (flipVal fuel' f)
      | .addU64 l r => .addU64 (flipVal fuel' l) (flipVal fuel' r)
      | .subU64 l r => .subU64 (flipVal fuel' l) (flipVal fuel' r)
      | .mulU64 l r => .mulU64 (flipVal fuel' l) (flipVal fuel' r)
      | .divU64 l r => .divU64 (flipVal fuel' l) (flipVal fuel' r)
      | .modU64 l r => .modU64 (flipVal fuel' l) (flipVal fuel' r)
      | .mapGetU64 b k => .mapGetU64 (flipVal fuel' b) (flipVal fuel' k)
      | .mapGetAddr b a0 a1 a2 =>
          .mapGetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
      | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
          .mapGetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1) (flipVal fuel' c2)
      | .ext kind operands => .ext kind (operands.map (flipVal fuel'))
  let rec flipOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      match op with
      | .letLocal i v => .letLocal i (flipVal fuel' v)
      | .joinLocal i => .joinLocal i
      | .setLocal i v => .setLocal i (flipVal fuel' v)
      | .returnState v => .returnState (flipVal fuel' v)
      | .returnU64 v => .returnU64 (flipVal fuel' v)
      | .storeField n v => .storeField n (flipVal fuel' v)
      | .okState v => .okState (flipVal fuel' v)
      | .checkedAddU64 l r => .checkedAddU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedSubU64 l r => .checkedSubU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedMulU64 l r => .checkedMulU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedDivU64 l r => .checkedDivU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedModU64 l r => .checkedModU64 (flipVal fuel' l) (flipVal fuel' r)
      | .ite c l r t f =>
        .ite c (flipVal fuel' l) (flipVal fuel' r)
          (t.map (flipOp fuel')) (f.map (flipOp fuel'))
      | .invoke prog metas data seed bump =>
        .invoke prog metas (data.map (·.map (flipVal fuel')))
          seed (bump.map (flipVal fuel'))
      | .ext (.svm (.component call)) =>
          .ext (.svm (.component (call.mapValues (flipVal fuel'))))
      | .ext (.xrpl payload) => .ext (.xrpl payload)
      | .ext (.near payload) =>
          .ext (.near (match payload with
            | .logUtf8 message => .logUtf8 message
            | .logUtf8Bounded capacity message =>
                .logUtf8Bounded capacity (message.map (flipVal fuel'))
            | .promiseFunctionCallDetached receiver method argsCapacity arguments
                depositLo depositHi gas =>
                .promiseFunctionCallDetached receiver method argsCapacity
                  (arguments.map (flipVal fuel')) (flipVal fuel' depositLo)
                  (flipVal fuel' depositHi) (flipVal fuel' gas)
            | .promiseFunctionCallReturned receiver method argsCapacity arguments
                depositLo depositHi gas =>
                .promiseFunctionCallReturned receiver method argsCapacity
                  (arguments.map (flipVal fuel')) (flipVal fuel' depositLo)
                  (flipVal fuel' depositHi) (flipVal fuel' gas)
            | .promiseTransferDetached receiver amountLo amountHi =>
                .promiseTransferDetached receiver
                  (flipVal fuel' amountLo) (flipVal fuel' amountHi)
            | .promiseTransferReturned receiver amountLo amountHi =>
                .promiseTransferReturned receiver
                  (flipVal fuel' amountLo) (flipVal fuel' amountHi)
            | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
                childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                childDepositLo childDepositHi childGas
                callbackDepositLo callbackDepositHi callbackGas =>
                .promiseFunctionCallThenReturned receiver childMethod callbackMethod
                  childArgsCapacity callbackArgsCapacity (childArguments.map (flipVal fuel'))
                  (callbackArguments.map (flipVal fuel')) (flipVal fuel' childDepositLo)
                  (flipVal fuel' childDepositHi) (flipVal fuel' childGas)
                  (flipVal fuel' callbackDepositLo) (flipVal fuel' callbackDepositHi)
                  (flipVal fuel' callbackGas)
            | .promiseFunctionCallAndThenReturned
                leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                leftArguments rightArguments callbackArguments
                leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
                callbackDepositLo callbackDepositHi callbackGas =>
                .promiseFunctionCallAndThenReturned
                  leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                  leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                  (leftArguments.map (flipVal fuel')) (rightArguments.map (flipVal fuel'))
                  (callbackArguments.map (flipVal fuel'))
                  (flipVal fuel' leftDepositLo) (flipVal fuel' leftDepositHi)
                  (flipVal fuel' leftGas) (flipVal fuel' rightDepositLo)
                  (flipVal fuel' rightDepositHi) (flipVal fuel' rightGas)
                  (flipVal fuel' callbackDepositLo) (flipVal fuel' callbackDepositHi)
                  (flipVal fuel' callbackGas)
            | .promiseResultRead capacity index =>
                .promiseResultRead capacity (flipVal fuel' index)
            | .transientBuffer64Begin capacity => .transientBuffer64Begin capacity
            | .transientBuffer64Set capacity index value =>
                .transientBuffer64Set capacity (flipVal fuel' index) (flipVal fuel' value)
            | .transientBuffer64Finish capacity => .transientBuffer64Finish capacity
            | .storageRead resultCapacity keyCapacity key =>
                .storageRead resultCapacity keyCapacity (key.map (flipVal fuel'))
            | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
                .storageWrite resultCapacity keyCapacity valueCapacity
                  (key.map (flipVal fuel')) (value.map (flipVal fuel'))
            | .storageRemove resultCapacity keyCapacity key =>
                .storageRemove resultCapacity keyCapacity (key.map (flipVal fuel'))
            | .storageHasKey resultCapacity keyCapacity key =>
                .storageHasKey resultCapacity keyCapacity (key.map (flipVal fuel'))
            | .reserved => .reserved))
      | .evmDeposit v => .evmDeposit (flipVal fuel' v)
      | .evmDeposit256 a0 a1 a2 a3 =>
          .evmDeposit256 (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2) (flipVal fuel' a3)
      | .evmSendEth a b c d =>
          .evmSendEth (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c) (flipVal fuel' d)
      | .evmSendEth256 a b c d0 d1 d2 d3 =>
          .evmSendEth256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d0) (flipVal fuel' d1) (flipVal fuel' d2) (flipVal fuel' d3)
      | .evmLog n v => .evmLog n (flipVal fuel' v)
      | .evmLogTransfer256 a b c d e f g0 g1 g2 g3 =>
          .evmLogTransfer256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g0) (flipVal fuel' g1) (flipVal fuel' g2) (flipVal fuel' g3)
      | .evmLogApproval256 a b c d e f g0 g1 g2 g3 =>
          .evmLogApproval256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g0) (flipVal fuel' g1) (flipVal fuel' g2) (flipVal fuel' g3)
      | .evmRevertInsufficient a b c d e f g h =>
          .evmRevertInsufficient (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g) (flipVal fuel' h)
      | .evmRevertUnauthorized a b c =>
          .evmRevertUnauthorized (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
      | .evmRevertZeroAddress => .evmRevertZeroAddress
      | .evmRevertPaused => .evmRevertPaused
      | .evmRevertCapExceeded => .evmRevertCapExceeded
      | .evmReceive => .evmReceive
      | .forAccum n v resultLocal => .forAccum n (flipVal fuel' v) resultLocal
      | .forBody n body => .forBody n (body.map (flipOp fuel'))
      | .indexSetLeaf n i v k leaf =>
          .indexSetLeaf n (flipVal fuel' i) (flipVal fuel' v) k leaf
      | .indexSet n i v k off =>
          .indexSet n (flipVal fuel' i) (flipVal fuel' v) k off
      | .mapGetU64 b k => .mapGetU64 (flipVal fuel' b) (flipVal fuel' k)
      | .mapSetU64 b k v =>
          .mapSetU64 (flipVal fuel' b) (flipVal fuel' k) (flipVal fuel' v)
      | .mapGetAddr b a0 a1 a2 =>
          .mapGetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
      | .mapSetAddr b a0 a1 a2 v =>
          .mapSetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' v)
      | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
          .mapGetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1) (flipVal fuel' c2)
      | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
          .mapSetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1)
            (flipVal fuel' c2) (flipVal fuel' v)
      | .mapSetAddr256 b a0 a1 a2 v0 v1 v2 v3 =>
          .mapSetAddr256 (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' v0) (flipVal fuel' v1)
            (flipVal fuel' v2) (flipVal fuel' v3)
      | .mapSetPair256 b a0 a1 a2 c0 c1 c2 v0 v1 v2 v3 =>
          .mapSetPair256 (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1)
            (flipVal fuel' c2) (flipVal fuel' v0) (flipVal fuel' v1)
            (flipVal fuel' v2) (flipVal fuel' v3)
      | .evmTokenTransfer a b c d e f g =>
          .evmTokenTransfer (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f) (flipVal fuel' g)
      | .evmTokenTransfer256 a b c d e f g0 g1 g2 g3 =>
          .evmTokenTransfer256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g0) (flipVal fuel' g1) (flipVal fuel' g2) (flipVal fuel' g3)
      | .evmTokenApprove256 a b c d e f g0 g1 g2 g3 =>
          .evmTokenApprove256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g0) (flipVal fuel' g1) (flipVal fuel' g2) (flipVal fuel' g3)
      | .evmTokenTransferFrom256 a b c d e f g h i j k l m =>
          .evmTokenTransferFrom256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f)
            (flipVal fuel' g) (flipVal fuel' h) (flipVal fuel' i)
            (flipVal fuel' j) (flipVal fuel' k) (flipVal fuel' l) (flipVal fuel' m)
      | .evmTokenBalanceOfSelf a b c =>
          .evmTokenBalanceOfSelf (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
      | .evmWethDeposit256 a b c d0 d1 d2 d3 =>
          .evmWethDeposit256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d0) (flipVal fuel' d1) (flipVal fuel' d2) (flipVal fuel' d3)
      | .evmWethWithdraw256 a b c d0 d1 d2 d3 =>
          .evmWethWithdraw256 (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d0) (flipVal fuel' d1) (flipVal fuel' d2) (flipVal fuel' d3)
      | .evmSwapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
          .evmSwapExact2 (flipVal fuel' r0) (flipVal fuel' r1) (flipVal fuel' r2)
            (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
            (flipVal fuel' b0) (flipVal fuel' b1) (flipVal fuel' b2)
            (flipVal fuel' i0) (flipVal fuel' i1) (flipVal fuel' i2) (flipVal fuel' i3)
            (flipVal fuel' m0) (flipVal fuel' m1) (flipVal fuel' m2) (flipVal fuel' m3)
      | .evmSwapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
          .evmSwapExact3 (flipVal fuel' r0) (flipVal fuel' r1) (flipVal fuel' r2)
            (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
            (flipVal fuel' b0) (flipVal fuel' b1) (flipVal fuel' b2)
            (flipVal fuel' c0) (flipVal fuel' c1) (flipVal fuel' c2)
            (flipVal fuel' i0) (flipVal fuel' i1) (flipVal fuel' i2) (flipVal fuel' i3)
            (flipVal fuel' m0) (flipVal fuel' m1) (flipVal fuel' m2) (flipVal fuel' m3)
      | .evmPermit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
          .evmPermit (flipVal fuel' o0) (flipVal fuel' o1) (flipVal fuel' o2)
            (flipVal fuel' s0) (flipVal fuel' s1) (flipVal fuel' s2)
            (flipVal fuel' v0) (flipVal fuel' v1) (flipVal fuel' v2) (flipVal fuel' v3)
            (flipVal fuel' d0) (flipVal fuel' d1) (flipVal fuel' d2) (flipVal fuel' d3)
            (flipVal fuel' vv)
            (flipVal fuel' r0) (flipVal fuel' r1) (flipVal fuel' r2) (flipVal fuel' r3)
            (flipVal fuel' z0) (flipVal fuel' z1) (flipVal fuel' z2) (flipVal fuel' z3)
      | .evmTokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
          .evmTokenPermit (flipVal fuel' t0) (flipVal fuel' t1) (flipVal fuel' t2)
            (flipVal fuel' o0) (flipVal fuel' o1) (flipVal fuel' o2)
            (flipVal fuel' s0) (flipVal fuel' s1) (flipVal fuel' s2)
            (flipVal fuel' v0) (flipVal fuel' v1) (flipVal fuel' v2) (flipVal fuel' v3)
            (flipVal fuel' d0) (flipVal fuel' d1) (flipVal fuel' d2) (flipVal fuel' d3)
            (flipVal fuel' vv)
            (flipVal fuel' r0) (flipVal fuel' r1) (flipVal fuel' r2) (flipVal fuel' r3)
            (flipVal fuel' z0) (flipVal fuel' z1) (flipVal fuel' z2) (flipVal fuel' z3)
      | .evmComponent call => .evmComponent (call.mapValues (flipVal fuel'))
      | .errorOverflow => .errorOverflow
      | .errorNamed n => .errorNamed n
      | .errorTyped frame => .errorTyped (frame.mapValues (flipVal fuel'))
  let ops := ops0.map (flipOp 128)
  let expandWide (ops : Array Ops.Op) (limbCount : Nat) : Array Ops.Op :=
    match ops.toList with
    | [.returnU64 (.ext kind operands)] =>
      if limbCount == 1 then #[.returnU64 (.ext kind operands)]
      else
        let names := #["w0", "w1", "w2", "w3"].extract 0 limbCount
        names.map fun n => .returnU64 (flattenField (.ext kind operands) n)
    | [.returnU64 v] =>
      let names := #["w0", "w1", "w2", "w3"].extract 0 limbCount
      names.map fun n => .returnU64 (flattenField v n)
    | _ => ops
  let ops :=
    let retTy := peelForalls info.type
    match codecScalarOfType retTy with
    | some (.uint bits) => if 64 < bits then expandWide ops ((bits + 63) / 64) else ops
    | some (.fixedBytes bytes) => expandWide ops ((bytes + 7) / 8)
    | some (.address 20) => expandWide ops 3
    | _ => ops
  let paramCount :=
    match kind with
    | .init => nLams
    | .increment | .get => if nLams ≤ 1 then 0 else nLams - 1
  let retTy := peelForalls info.type
  let paramSchemas ← inferParamSchemas env e kind
  unless paramSchemas.size == paramCount do
    throw "extract/unsupported: boundary parameter schema count mismatch"
  let paramTypes := scalarTypesOfSchemas paramSchemas
  let paramWidths := paramTypes.map legacyWidthOfScalar
  let retSchema ← logicalReturnSchema env kind retTy
  let ops ← expandBoundedReturnOps retSchema ops
  let ops ← expandTaggedReturnOps retSchema ops
  let ops ← expandStaticRecordReturnOps retSchema ops
  let retWidths :=
    match kind with
    | .get =>
      if isAddr20Type retTy then #[20]
      else if isUInt128Type retTy then #[16]
      else if isUInt256Type retTy then #[32]
      else if isBytes32Type retTy then #[33]
      else if let some bytes := fixedBytesSize? retTy then #[bytes]
      else if widthOfType retTy == some 1 then #[1]
      else if widthOfType retTy == some 2 then #[2]
      else if widthOfType retTy == some 4 then #[4]
      else #[]
    | _ => #[]
  let rec maxReturnCount (fuel : Nat) (ops : Array Ops.Op) : Nat :=
    match fuel with
    | 0 => 0
    | fuel' + 1 =>
      let direct := ops.foldl (init := 0) fun count op =>
        match op with | .returnU64 _ => count + 1 | _ => count
      let nested := ops.foldl (init := 0) fun count op =>
        match op with
        | .ite _ _ _ thn els => max count (max (maxReturnCount fuel' thn) (maxReturnCount fuel' els))
        | .forBody _ body => max count (maxReturnCount fuel' body)
        | _ => count
      max direct nested
  let retCount :=
    match kind with
    | .get =>
      if isAddr20Type retTy then 3
      else if isUInt128Type retTy then 2
      else if isUInt256Type retTy then 4
      else if let some bytes := fixedBytesSize? retTy then (bytes + 7) / 8
      else
        let nRet := ops.foldl (init := 0) fun acc op =>
          match op with | .returnU64 _ => acc + 1 | _ => acc
        let nRet := max nRet (maxReturnCount 32 ops)
        if nRet = 0 then 1 else nRet
    | .increment =>
      let nRet := maxReturnCount 32 ops
      if nRet = 0 then 1 else nRet
    | .init => 1
  let retTypes :=
    match retSchema with
    | .scalar type => #[type]
    | _ => #[]
  let annotations :=
    (Attr.svmRawEntries env n).map (·.annotation) ++ Attr.nearEntryAnnotations env n
  return {
    kind, name := n.toString, ixName := Core.IR.ixNameOfLean lean
    paramCount, paramWidths, paramTypes, paramSchemas, retWidths, retTypes, retSchema, retCount,
    annotations, sketch, ops
  }

private def isUInt64Type (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some ``UInt64

private structure SchemaFragment where
  leaves : Array Core.Leaf := #[]
  vectors : Array Core.VectorLayout := #[]

private def SchemaFragment.byteWidth (fragment : SchemaFragment) : Nat :=
  fragment.leaves.foldl (init := 0) fun width leaf => width + leaf.width

private def scalarFragment (name : String) (place : Core.Place)
    (ty : Core.ScalarTy) : SchemaFragment :=
  { leaves := #[{ place, name, ty }] }

private def optionFragment (name : String) (place : Core.Place) : SchemaFragment :=
  { leaves := #[
      { place := place.push .optionTag, name := s!"{name}_tag", ty := .optionTag },
      { place := place.push .optionPayload, name := s!"{name}_p0", ty := .uint 64 }
    ] }

private def variantFragment (typeName name : String) (place : Core.Place)
    (payloadWidth : Nat) : SchemaFragment := Id.run do
  let mut leaves : Array Core.Leaf :=
    #[{ place := place.push .variantTag, name := s!"{name}_tag", ty := .variantTag typeName }]
  for index in [:payloadWidth] do
    leaves := leaves.push {
      place := place.push (.variantPayload index)
      name := s!"{name}_p{index}"
      ty := .uint 64
    }
  return { leaves }

private def leafSchema (env : Environment) (fuel : Nat) (name : String)
    (place : Core.Place) (ty : Expr) : Except String SchemaFragment :=
  match fuel with
  | 0 => .error s!"extract/unsupported: field {name} nest depth"
  | fuel' + 1 =>
    let ty := ty.consumeMData
    if ty.getAppFn.constName? == some ``UInt64 then
      .ok (scalarFragment name place (.uint 64))
    else if ty.getAppFn.constName? == some ``UInt32 then
      .ok (scalarFragment name place (.uint 32))
    else if ty.getAppFn.constName? == some ``UInt16 then
      .ok (scalarFragment name place (.uint 16))
    else if ty.getAppFn.constName? == some ``UInt8 then
      .ok (scalarFragment name place (.uint 8))
    else if ty.getAppFn.constName? == some addr20Name then
      .ok {
        leaves := #[
          { place := place.push (.field "Addr20" 0 "w0"), name := s!"{name}_w0", ty := .uint 64 },
          { place := place.push (.field "Addr20" 1 "w1"), name := s!"{name}_w1", ty := .uint 64 },
          { place := place.push (.field "Addr20" 2 "w2"), name := s!"{name}_w2", ty := .uint 64 }
        ]
      }
    else if isUInt256Type ty then
      .ok {
        leaves := #[
          { place := place.push (.field "UInt256" 0 "w0"), name := s!"{name}_w0", ty := .uint 64 },
          { place := place.push (.field "UInt256" 1 "w1"), name := s!"{name}_w1", ty := .uint 64 },
          { place := place.push (.field "UInt256" 2 "w2"), name := s!"{name}_w2", ty := .uint 64 },
          { place := place.push (.field "UInt256" 3 "w3"), name := s!"{name}_w3", ty := .uint 64 }
        ]
      }
    else if ty.getAppFn.constName? == some ``Option then
      let args := ty.getAppArgs
      if args.size ≥ 1 && args[args.size - 1]!.consumeMData.getAppFn.constName? == some ``UInt64 then
        .ok (optionFragment name place)
      else
        .error s!"extract/unsupported: field {name} is not Option UInt64"
    else if ty.getAppFn.constName? == some ``Vector then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        match asLit 8 args[args.size - 1]! with
        | some (.lit n) =>
          if n.toNat = 0 then
            .error s!"extract/unsupported: field {name} Vector length 0"
          else
            Id.run do
              let mut leaves : Array Core.Leaf := #[]
              let mut vectors : Array Core.VectorLayout := #[]
              let mut elementBytes : Nat := 0
              let mut elementLeaves : Nat := 0
              for i in List.range n.toNat do
                let itemPlace := place.push (.index i)
                match leafSchema env fuel' s!"{name}_{i}" itemPlace args[args.size - 2]! with
                | .error reason => return .error reason
                | .ok item =>
                    if i == 0 then
                      elementBytes := item.byteWidth
                      elementLeaves := item.leaves.size
                    leaves := leaves ++ item.leaves
                    vectors := vectors ++ item.vectors
              let vector : Core.VectorLayout := {
                place, name, length := n.toNat, elementBytes, elementLeaves
              }
              return .ok { leaves, vectors := #[vector] ++ vectors }
        | _ => .error s!"extract/unsupported: field {name} Vector length is not a literal"
      else
        .error s!"extract/unsupported: field {name} is not Vector UInt64 n"
    else if ty.getAppFn.constName? == some ``Array then
      .error s!"extract/unsupported: field {name} Array is not fixed-length; use Vector"
    else if ty.getAppFn.constName? == some ``Bool then
      .ok (scalarFragment name place .bool)
    else if let some tyName := ty.getAppFn.constName? then
      if isEnumLeaf env tyName then
        .ok (scalarFragment name place (.enum tyName.toString))
      else if isUInt64Newtype env tyName then
        .ok (scalarFragment name place (.newtype tyName.toString 64))
      else if isOptionLikeInductive env tyName then
        .ok (optionFragment name place)
      else if let some payloadWidth := uint64VariantPayloadWidth? env tyName then
        .ok (variantFragment tyName.toString name place payloadWidth)
      else if isUserName env tyName && isStructure env tyName &&
          !(isEnumLeaf env tyName) && !(isOptionLikeInductive env tyName) then
        if !(getStructureParentInfo env tyName).isEmpty then
          .error s!"extract/unsupported: field {name} record inheritance"
        else
          let fields := getStructureFields env tyName
          if fields.isEmpty then
            .error s!"extract/unsupported: field {name} record has no fields"
          else
            Id.run do
              let mut acc : SchemaFragment := {}
              let mut ordinal : Nat := 0
              for f in fields do
                if (isSubobjectField? env tyName f).isSome then
                  return .error s!"extract/unsupported: field {name} record inheritance"
                let some fty := fieldTypeExpr env tyName f
                  | return .error s!"extract/unsupported: field {name}.{f} has no type"
                let childPlace := place.push (.field tyName.toString ordinal f.toString)
                match leafSchema env fuel' s!"{name}_{f}" childPlace fty with
                | .error r => return .error r
                | .ok fragment =>
                    acc := {
                      leaves := acc.leaves ++ fragment.leaves
                      vectors := acc.vectors ++ fragment.vectors
                    }
                ordinal := ordinal + 1
              return .ok acc
      else if match env.find? tyName with | some (.inductInfo _) => true | _ => false then
        .error s!"extract/unsupported: field {name} enum has payload"
      else
        .error s!"extract/unsupported: field {name} is not a supported leaf"
    else
      .error s!"extract/unsupported: field {name} is not a supported leaf"

/-- `Examples.Counter.init` → `Counter`。 -/
def programNameOfInit (n : Name) : String :=
  match n with
  | .str (.str _ mod) "init" => mod
  | .str _ "init" => "Program"
  | _ => "Program"

/-- 从 `init` 返回类型收 typed state schema。无 `extends`。 -/
def inferSchema (env : Environment) (initName : Name) : Except String Core.Schema := do
  let some info := env.find? initName
    | throw s!"extract/unsupported: unknown {initName}"
  let some structName := (peelForalls info.type).getAppFn.constName?
    | throw "extract/unsupported: init return is not a structure"
  unless isStructure env structName do
    throw s!"extract/unsupported: init return is not a structure {structName}"
  unless (getStructureParentInfo env structName).isEmpty do
    throw "extract/unsupported: record inheritance"
  let names := getStructureFields env structName
  if names.isEmpty then
    throw "extract/unsupported: structure has no fields"
  let mut leaves : Array Core.Leaf := #[]
  let mut vectors : Array Core.VectorLayout := #[]
  let mut ordinal : Nat := 0
  for n in names do
    if (isSubobjectField? env structName n).isSome then
      throw "extract/unsupported: record inheritance"
    let some ty := fieldTypeExpr env structName n
      | throw s!"extract/unsupported: field {n} has no type"
    let place : Core.Place := {
      steps := #[.field structName.toString ordinal n.toString]
    }
    let fragment ← leafSchema env 8 n.toString place ty
    leaves := leaves ++ fragment.leaves
    vectors := vectors ++ fragment.vectors
    ordinal := ordinal + 1
  return { rootType := structName.toString, leaves, vectors }

/-- Target-neutral physical slots are a derived view of the typed schema. -/
def inferSlots (env : Environment) (initName : Name) : Except String (Array Core.IR.Slot) := do
  return Core.IR.slotsOfSchema (← inferSchema env initName)

def inferFields (env : Environment) (initName : Name) : Except String (Array String) := do
  return (← inferSlots env initName).map (·.name)

private structure FieldUse where
  name : String
  rootArg? : Option Nat := none

private partial def valFields : Ops.Val → Array FieldUse
  | .field (.arg i) n =>
      if n == "w0" || n == "w1" || n == "w2" || n == "w3" then #[]
      else #[{ name := n, rootArg? := some i }]
  | .field (.local _) n =>
      if n == "w0" || n == "w1" || n == "w2" || n == "w3" then #[] else #[{ name := n }]
  | .field _ n => #[{ name := n }]
  | .arg _ => #[]
  | .local _ => #[]
  | .lit _ => #[]
  | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
  | .accN | .isSigner0 | .isWritable0 | .isExecutable0
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
  | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
  | .accKeyWord _ _ | .accOwnerWord _ _ | .accDataWord _ _
  | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
  | .signerKeyN _ | .ownerIsSelf _ | .findPdaSeeds _ | .checkPdaSeeds _ _ => #[]
  | .byteSwap64 word => valFields word
  | .accDataWordAt _ _ _ _ i => valFields i
  | .ext (.svm (.component _)) operands => operands.flatMap valFields
  | .checkPda _ b => valFields b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      valFields l ++ valFields r
  | .bitNot v => valFields v
  | .indexGet b _ i _ => valFields b ++ valFields i
  | .loopIx => #[]
  | .select _ l r t f => valFields l ++ valFields r ++ valFields t ++ valFields f
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      valFields l ++ valFields r
  | .mapGetU64 b k => valFields b ++ valFields k
  | .mapGetAddr b a0 a1 a2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2
  | v => if Ops.hasEvmLeaf #[.returnU64 v] then #[] else #[]

private def opFields : Ops.Op → Array FieldUse
  | .letLocal _ v => valFields v
  | .joinLocal _ => #[]
  | .setLocal _ v => valFields v
  | .checkedAddU64 l r => valFields l ++ valFields r
  | .checkedSubU64 l r => valFields l ++ valFields r
  | .checkedMulU64 l r => valFields l ++ valFields r
  | .checkedDivU64 l r => valFields l ++ valFields r
  | .checkedModU64 l r => valFields l ++ valFields r
  | .ite _ l r t f =>
      valFields l ++ valFields r ++ t.flatMap opFields ++ f.flatMap opFields
  | .invoke _ _ data _ bump =>
      (data.flatMap fun word => word.value?.map valFields |>.getD #[]) ++
        (match bump with | some v => valFields v | none => #[])
  | .ext (.svm (.component call)) => call.values.flatMap valFields
  | .ext (.xrpl _) => #[]
  | .ext (.near _) => #[]
  | .evmDeposit v => valFields v
  | .evmDeposit256 a0 a1 a2 a3 =>
      valFields a0 ++ valFields a1 ++ valFields a2 ++ valFields a3
  | .evmSendEth a b c d => valFields a ++ valFields b ++ valFields c ++ valFields d
  | .evmSendEth256 a b c d0 d1 d2 d3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d0 ++
        valFields d1 ++ valFields d2 ++ valFields d3
  | .evmLog _ v => valFields v
  | .evmLogTransfer256 a b c d e f g0 g1 g2 g3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++ valFields e ++
        valFields f ++ valFields g0 ++ valFields g1 ++ valFields g2 ++ valFields g3
  | .evmLogApproval256 a b c d e f g0 g1 g2 g3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++ valFields e ++
        valFields f ++ valFields g0 ++ valFields g1 ++ valFields g2 ++ valFields g3
  | .evmRevertInsufficient a b c d e f g h =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g ++ valFields h
  | .evmRevertUnauthorized a b c => valFields a ++ valFields b ++ valFields c
  | .evmRevertZeroAddress => #[]
  | .evmRevertPaused => #[]
  | .evmRevertCapExceeded => #[]
  | .evmReceive => #[]
  | .forAccum _ v _ => valFields v
  | .forBody _ body => body.flatMap opFields
  | .indexSetLeaf _ i v _ _ | .indexSet _ i v _ _ => valFields i ++ valFields v
  | .storeField n v => #[{ name := n }] ++ valFields v
  | .mapGetU64 b k => valFields b ++ valFields k
  | .mapSetU64 b k v => valFields b ++ valFields k ++ valFields v
  | .mapGetAddr b a0 a1 a2 => valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2
  | .mapSetAddr b a0 a1 a2 v =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++ valFields v
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2
  | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2 ++ valFields v
  | .mapSetAddr256 b a0 a1 a2 v0 v1 v2 v3 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields v0 ++ valFields v1 ++ valFields v2 ++ valFields v3
  | .mapSetPair256 b a0 a1 a2 c0 c1 c2 v0 v1 v2 v3 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2 ++
        valFields v0 ++ valFields v1 ++ valFields v2 ++ valFields v3
  | .evmTokenTransfer a b c d e f g =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g
  | .evmTokenTransfer256 a b c d e f g0 g1 g2 g3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g0 ++ valFields g1 ++
        valFields g2 ++ valFields g3
  | .evmTokenApprove256 a b c d e f g0 g1 g2 g3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g0 ++ valFields g1 ++
        valFields g2 ++ valFields g3
  | .evmTokenTransferFrom256 a b c d e f g h i j k l m =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g ++ valFields h ++
        valFields i ++ valFields j ++ valFields k ++ valFields l ++ valFields m
  | .evmTokenBalanceOfSelf a b c => valFields a ++ valFields b ++ valFields c
  | .evmWethDeposit256 a b c d0 d1 d2 d3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d0 ++
        valFields d1 ++ valFields d2 ++ valFields d3
  | .evmWethWithdraw256 a b c d0 d1 d2 d3 =>
      valFields a ++ valFields b ++ valFields c ++ valFields d0 ++
        valFields d1 ++ valFields d2 ++ valFields d3
  | .evmSwapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      valFields r0 ++ valFields r1 ++ valFields r2 ++
        valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields b0 ++ valFields b1 ++ valFields b2 ++
        valFields i0 ++ valFields i1 ++ valFields i2 ++ valFields i3 ++
        valFields m0 ++ valFields m1 ++ valFields m2 ++ valFields m3
  | .evmSwapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      valFields r0 ++ valFields r1 ++ valFields r2 ++
        valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields b0 ++ valFields b1 ++ valFields b2 ++
        valFields c0 ++ valFields c1 ++ valFields c2 ++
        valFields i0 ++ valFields i1 ++ valFields i2 ++ valFields i3 ++
        valFields m0 ++ valFields m1 ++ valFields m2 ++ valFields m3
  | .evmPermit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      valFields o0 ++ valFields o1 ++ valFields o2 ++
        valFields s0 ++ valFields s1 ++ valFields s2 ++
        valFields v0 ++ valFields v1 ++ valFields v2 ++ valFields v3 ++
        valFields d0 ++ valFields d1 ++ valFields d2 ++ valFields d3 ++
        valFields vv ++
        valFields r0 ++ valFields r1 ++ valFields r2 ++ valFields r3 ++
        valFields z0 ++ valFields z1 ++ valFields z2 ++ valFields z3
  | .evmTokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      valFields t0 ++ valFields t1 ++ valFields t2 ++
        valFields o0 ++ valFields o1 ++ valFields o2 ++
        valFields s0 ++ valFields s1 ++ valFields s2 ++
        valFields v0 ++ valFields v1 ++ valFields v2 ++ valFields v3 ++
        valFields d0 ++ valFields d1 ++ valFields d2 ++ valFields d3 ++
        valFields vv ++
        valFields r0 ++ valFields r1 ++ valFields r2 ++ valFields r3 ++
        valFields z0 ++ valFields z1 ++ valFields z2 ++ valFields z3
  | .evmComponent call => call.values.flatMap valFields
  | .okState v => valFields v
  | .errorOverflow => #[]
  | .errorNamed _ => #[]
  | .errorTyped frame => frame.values.flatMap valFields
  | .returnU64 v => valFields v
  | .returnState v => valFields v

private def vectorLeafOffset? (schema : Core.Schema) (name leaf : String) : Option Nat :=
  match schema.vector? name with
  | none => none
  | some vector => Id.run do
      let mut offset := 0
      for item in schema.vectorElementLeaves vector do
        if vector.relativeLeafName item == leaf then return some offset
        offset := offset + item.width
      return none

/-- Resolve logical dynamic-vector leaves exactly once, against the typed source schema. -/
private def resolveVectorLeaves (p : IR.Program) : Except String IR.Program := do
  let resolve (name leaf : String) : Except String Nat :=
    match vectorLeafOffset? p.schema name leaf with
    | some offset => pure offset
    | none => throw s!"extract/unsupported: vector {name} has no leaf {leaf}"
  let rec goVal (fuel : Nat) (v : Ops.Val) : Except String Ops.Val :=
    match fuel with
    | 0 => throw "extract/unsupported: value nesting exceeds schema resolution limit"
    | fuel' + 1 =>
      match v with
      | .arg _ | .local _ | .lit _ | .loopIx => pure v
      | .field (.indexGet b n i k _) leaf =>
          return .indexGet (← goVal fuel' b) n (← goVal fuel' i) k (← resolve n leaf)
      | .field b n => return .field (← goVal fuel' b) n
      | .bitAnd l r => return .bitAnd (← goVal fuel' l) (← goVal fuel' r)
      | .bitOr l r => return .bitOr (← goVal fuel' l) (← goVal fuel' r)
      | .bitXor l r => return .bitXor (← goVal fuel' l) (← goVal fuel' r)
      | .bitNot value => return .bitNot (← goVal fuel' value)
      | .shiftL l r => return .shiftL (← goVal fuel' l) (← goVal fuel' r)
      | .shiftR l r => return .shiftR (← goVal fuel' l) (← goVal fuel' r)
      | .indexGet b n i k off =>
          return .indexGet (← goVal fuel' b) n (← goVal fuel' i) k off
      | .select c l r t f =>
          return .select c (← goVal fuel' l) (← goVal fuel' r)
            (← goVal fuel' t) (← goVal fuel' f)
      | .addU64 l r => return .addU64 (← goVal fuel' l) (← goVal fuel' r)
      | .subU64 l r => return .subU64 (← goVal fuel' l) (← goVal fuel' r)
      | .mulU64 l r => return .mulU64 (← goVal fuel' l) (← goVal fuel' r)
      | .divU64 l r => return .divU64 (← goVal fuel' l) (← goVal fuel' r)
      | .modU64 l r => return .modU64 (← goVal fuel' l) (← goVal fuel' r)
      | .ext kind operands => return .ext kind (← operands.mapM (goVal fuel'))
  let normalizeVal := goVal 128
  let rec goOp (fuel : Nat) (op : Ops.Op) : Except String Ops.Op :=
    match fuel with
    | 0 => throw "extract/unsupported: control-flow nesting exceeds schema resolution limit"
    | fuel' + 1 =>
      match op with
      | .letLocal i v => return .letLocal i (← normalizeVal v)
      | .joinLocal i => pure (.joinLocal i)
      | .setLocal i v => return .setLocal i (← normalizeVal v)
      | .checkedAddU64 l r => return .checkedAddU64 (← normalizeVal l) (← normalizeVal r)
      | .checkedSubU64 l r => return .checkedSubU64 (← normalizeVal l) (← normalizeVal r)
      | .checkedMulU64 l r => return .checkedMulU64 (← normalizeVal l) (← normalizeVal r)
      | .checkedDivU64 l r => return .checkedDivU64 (← normalizeVal l) (← normalizeVal r)
      | .checkedModU64 l r => return .checkedModU64 (← normalizeVal l) (← normalizeVal r)
      | .indexSetLeaf n i v k leaf =>
          return .indexSet n (← normalizeVal i) (← normalizeVal v) k (← resolve n leaf)
      | .indexSet n i v k off =>
          return .indexSet n (← normalizeVal i) (← normalizeVal v) k off
      | .ite c l r t f =>
          return .ite c (← normalizeVal l) (← normalizeVal r)
            (← t.mapM (goOp fuel')) (← f.mapM (goOp fuel'))
      | .forAccum n v resultLocal => return .forAccum n (← normalizeVal v) resultLocal
      | .forBody n body => return .forBody n (← body.mapM (goOp fuel'))
      | .storeField n v => return .storeField n (← normalizeVal v)
      | .okState v => return .okState (← normalizeVal v)
      | .errorOverflow => pure .errorOverflow
      | .errorNamed n => pure (.errorNamed n)
      | .errorTyped frame => return .errorTyped (← frame.mapValuesM normalizeVal)
      | .returnU64 v => return .returnU64 (← normalizeVal v)
      | .returnState v => return .returnState (← normalizeVal v)
      | .invoke programIx metas data seed bump =>
          return .invoke programIx metas (← data.mapM fun word =>
            match word.value? with
            | some value => do
                let normalized ← normalizeVal value
                pure (word.map fun _ => normalized)
            | none => pure (word.map id)) seed (← bump.mapM normalizeVal)
      | .ext (.svm (.component call)) =>
          return .ext (.svm (.component (← call.mapValuesM normalizeVal)))
      | .ext (.xrpl payload) => pure (.ext (.xrpl payload))
      | .ext (.near payload) => pure (.ext (.near payload))
      | .evmDeposit v => return .evmDeposit (← normalizeVal v)
      | .evmDeposit256 a0 a1 a2 a3 =>
          return .evmDeposit256 (← normalizeVal a0) (← normalizeVal a1)
            (← normalizeVal a2) (← normalizeVal a3)
      | .evmSendEth a b c d =>
          return .evmSendEth (← normalizeVal a) (← normalizeVal b)
            (← normalizeVal c) (← normalizeVal d)
      | .evmSendEth256 a b c d0 d1 d2 d3 =>
          return .evmSendEth256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d0) (← normalizeVal d1) (← normalizeVal d2) (← normalizeVal d3)
      | .evmLog n v => return .evmLog n (← normalizeVal v)
      | .evmLogTransfer256 a b c d e f g0 g1 g2 g3 =>
          return .evmLogTransfer256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g0) (← normalizeVal g1) (← normalizeVal g2) (← normalizeVal g3)
      | .evmLogApproval256 a b c d e f g0 g1 g2 g3 =>
          return .evmLogApproval256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g0) (← normalizeVal g1) (← normalizeVal g2) (← normalizeVal g3)
      | .evmRevertInsufficient a b c d e f g h =>
          return .evmRevertInsufficient (← normalizeVal a) (← normalizeVal b)
            (← normalizeVal c) (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g) (← normalizeVal h)
      | .evmRevertUnauthorized a b c =>
          return .evmRevertUnauthorized (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
      | .evmRevertZeroAddress => pure .evmRevertZeroAddress
      | .evmRevertPaused => pure .evmRevertPaused
      | .evmRevertCapExceeded => pure .evmRevertCapExceeded
      | .evmReceive => pure .evmReceive
      | .mapGetU64 b k => return .mapGetU64 (← normalizeVal b) (← normalizeVal k)
      | .mapSetU64 b k v =>
          return .mapSetU64 (← normalizeVal b) (← normalizeVal k) (← normalizeVal v)
      | .mapGetAddr b a0 a1 a2 =>
          return .mapGetAddr (← normalizeVal b) (← normalizeVal a0)
            (← normalizeVal a1) (← normalizeVal a2)
      | .mapSetAddr b a0 a1 a2 v =>
          return .mapSetAddr (← normalizeVal b) (← normalizeVal a0)
            (← normalizeVal a1) (← normalizeVal a2) (← normalizeVal v)
      | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
          return .mapGetPair (← normalizeVal b) (← normalizeVal a0) (← normalizeVal a1)
            (← normalizeVal a2) (← normalizeVal c0) (← normalizeVal c1) (← normalizeVal c2)
      | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
          return .mapSetPair (← normalizeVal b) (← normalizeVal a0) (← normalizeVal a1)
            (← normalizeVal a2) (← normalizeVal c0) (← normalizeVal c1) (← normalizeVal c2)
            (← normalizeVal v)
      | .mapSetAddr256 b a0 a1 a2 v0 v1 v2 v3 =>
          return .mapSetAddr256 (← normalizeVal b) (← normalizeVal a0) (← normalizeVal a1)
            (← normalizeVal a2) (← normalizeVal v0) (← normalizeVal v1)
            (← normalizeVal v2) (← normalizeVal v3)
      | .mapSetPair256 b a0 a1 a2 c0 c1 c2 v0 v1 v2 v3 =>
          return .mapSetPair256 (← normalizeVal b) (← normalizeVal a0) (← normalizeVal a1)
            (← normalizeVal a2) (← normalizeVal c0) (← normalizeVal c1) (← normalizeVal c2)
            (← normalizeVal v0) (← normalizeVal v1) (← normalizeVal v2) (← normalizeVal v3)
      | .evmTokenTransfer a b c d e f g =>
          return .evmTokenTransfer (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f) (← normalizeVal g)
      | .evmTokenTransfer256 a b c d e f g0 g1 g2 g3 =>
          return .evmTokenTransfer256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g0) (← normalizeVal g1) (← normalizeVal g2) (← normalizeVal g3)
      | .evmTokenApprove256 a b c d e f g0 g1 g2 g3 =>
          return .evmTokenApprove256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g0) (← normalizeVal g1) (← normalizeVal g2) (← normalizeVal g3)
      | .evmTokenTransferFrom256 a b c d e f g h i j k l m =>
          return .evmTokenTransferFrom256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d) (← normalizeVal e) (← normalizeVal f)
            (← normalizeVal g) (← normalizeVal h) (← normalizeVal i)
            (← normalizeVal j) (← normalizeVal k) (← normalizeVal l) (← normalizeVal m)
      | .evmTokenBalanceOfSelf a b c =>
          return .evmTokenBalanceOfSelf (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
      | .evmWethDeposit256 a b c d0 d1 d2 d3 =>
          return .evmWethDeposit256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d0) (← normalizeVal d1) (← normalizeVal d2) (← normalizeVal d3)
      | .evmWethWithdraw256 a b c d0 d1 d2 d3 =>
          return .evmWethWithdraw256 (← normalizeVal a) (← normalizeVal b) (← normalizeVal c)
            (← normalizeVal d0) (← normalizeVal d1) (← normalizeVal d2) (← normalizeVal d3)
      | .evmSwapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
          return .evmSwapExact2 (← normalizeVal r0) (← normalizeVal r1) (← normalizeVal r2)
            (← normalizeVal a0) (← normalizeVal a1) (← normalizeVal a2)
            (← normalizeVal b0) (← normalizeVal b1) (← normalizeVal b2)
            (← normalizeVal i0) (← normalizeVal i1) (← normalizeVal i2) (← normalizeVal i3)
            (← normalizeVal m0) (← normalizeVal m1) (← normalizeVal m2) (← normalizeVal m3)
      | .evmSwapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
          return .evmSwapExact3 (← normalizeVal r0) (← normalizeVal r1) (← normalizeVal r2)
            (← normalizeVal a0) (← normalizeVal a1) (← normalizeVal a2)
            (← normalizeVal b0) (← normalizeVal b1) (← normalizeVal b2)
            (← normalizeVal c0) (← normalizeVal c1) (← normalizeVal c2)
            (← normalizeVal i0) (← normalizeVal i1) (← normalizeVal i2) (← normalizeVal i3)
            (← normalizeVal m0) (← normalizeVal m1) (← normalizeVal m2) (← normalizeVal m3)
      | .evmPermit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
          return .evmPermit (← normalizeVal o0) (← normalizeVal o1) (← normalizeVal o2)
            (← normalizeVal s0) (← normalizeVal s1) (← normalizeVal s2)
            (← normalizeVal v0) (← normalizeVal v1) (← normalizeVal v2) (← normalizeVal v3)
            (← normalizeVal d0) (← normalizeVal d1) (← normalizeVal d2) (← normalizeVal d3)
            (← normalizeVal vv)
            (← normalizeVal r0) (← normalizeVal r1) (← normalizeVal r2) (← normalizeVal r3)
            (← normalizeVal z0) (← normalizeVal z1) (← normalizeVal z2) (← normalizeVal z3)
      | .evmTokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
          return .evmTokenPermit (← normalizeVal t0) (← normalizeVal t1) (← normalizeVal t2)
            (← normalizeVal o0) (← normalizeVal o1) (← normalizeVal o2)
            (← normalizeVal s0) (← normalizeVal s1) (← normalizeVal s2)
            (← normalizeVal v0) (← normalizeVal v1) (← normalizeVal v2) (← normalizeVal v3)
            (← normalizeVal d0) (← normalizeVal d1) (← normalizeVal d2) (← normalizeVal d3)
            (← normalizeVal vv)
            (← normalizeVal r0) (← normalizeVal r1) (← normalizeVal r2) (← normalizeVal r3)
            (← normalizeVal z0) (← normalizeVal z1) (← normalizeVal z2) (← normalizeVal z3)
      | .evmComponent call =>
          return .evmComponent (← call.mapValuesM normalizeVal)
  return { p with methods := ← p.methods.mapM fun m => do
    return { m with ops := ← m.ops.mapM (goOp 128) } }

/-- Make state writeback explicit once, after source schema and normalized Ops are both available. -/
private def evaluateProgram (p : IR.Program) : Except String IR.Program := do
  let mut methods := #[]
  for method in p.methods do
    let evaluation ←
      match Core.evaluate p.schema method.ops with
      | .ok evaluation => pure evaluation
      | .error reason => throw s!"{method.ixName}: {reason}"
    methods := methods.push { method with evaluation }
  return { p with methods }

private def checkUsedFields (p : IR.Program) : Except String Unit := do
  for m in p.methods do
    for op in m.ops do
      for field in opFields op do
        if let some rootArg := field.rootArg? then
          if rootArg < m.paramCount then continue
        if (Core.IR.fieldWidth p field.name).isNone then
          throw s!"{m.ixName}: extract/unsupported: unknown field {field.name}"

/-- Typed initializers must account for every leaf; backends must never invent missing zeros. -/
private def checkInitCoverage (p : IR.Program) : Except String Unit := do
  for method in p.methods do
    if method.kind == .init then
      let count := method.ops.foldl (init := 0) fun total op =>
        match op with | .returnState _ => total + 1 | _ => total
      unless count == p.schema.leaves.size do
        throw (s!"extract/unsupported: {method.ixName} initializes {count} state leaves, " ++
          s!"schema requires {p.schema.leaves.size}")

private partial def valEscapedArg (limit : Nat) : Ops.Val → Option Nat
  | .arg i => if i < limit then none else some i
  | .field b _ | .bitNot b | .checkPda _ b => valEscapedArg limit b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
  | .mapGetU64 l r => #[l, r].findSome? (valEscapedArg limit)
  | .indexGet b _ i _ => #[b, i].findSome? (valEscapedArg limit)
  | .select _ l r t f => #[l, r, t, f].findSome? (valEscapedArg limit)
  | .mapGetAddr a b c d => #[a, b, c, d].findSome? (valEscapedArg limit)
  | .mapGetPair a b c d e f g =>
      #[a, b, c, d, e, f, g].findSome? (valEscapedArg limit)
  | _ => none

private partial def opEscapedArg (limit : Nat) : Ops.Op → Option Nat
  | .letLocal _ v => valEscapedArg limit v
  | .joinLocal _ => none
  | .setLocal _ v => valEscapedArg limit v
  | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
  | .checkedDivU64 l r | .checkedModU64 l r =>
      #[l, r].findSome? (valEscapedArg limit)
  | .ite _ l r t f =>
      #[l, r].findSome? (valEscapedArg limit) <|>
        t.findSome? (opEscapedArg limit) <|> f.findSome? (opEscapedArg limit)
  | .invoke _ _ data _ bump =>
      (data.findSome? fun word => word.value?.bind (valEscapedArg limit)) <|>
        bump.bind (valEscapedArg limit)
  | .ext (.svm (.component call)) =>
      call.values.findSome? (valEscapedArg limit)
  | .ext (.xrpl _) => none
  | .ext (.near _) => none
  | .evmDeposit v | .evmLog _ v | .forAccum _ v _ => valEscapedArg limit v
  | .evmDeposit256 a0 a1 a2 a3 => #[a0, a1, a2, a3].findSome? (valEscapedArg limit)
  | .evmSendEth a b c d => #[a, b, c, d].findSome? (valEscapedArg limit)
  | .evmSendEth256 a b c d0 d1 d2 d3 =>
      #[a, b, c, d0, d1, d2, d3].findSome? (valEscapedArg limit)
  | .evmLogTransfer256 a b c d e f g h i j =>
      #[a, b, c, d, e, f, g, h, i, j].findSome? (valEscapedArg limit)
  | .evmLogApproval256 a b c d e f g h i j =>
      #[a, b, c, d, e, f, g, h, i, j].findSome? (valEscapedArg limit)
  | .evmRevertInsufficient a b c d e f g h =>
      #[a, b, c, d, e, f, g, h].findSome? (valEscapedArg limit)
  | .evmRevertUnauthorized a b c =>
      #[a, b, c].findSome? (valEscapedArg limit)
  | .evmRevertZeroAddress => none
  | .evmRevertPaused => none
  | .evmRevertCapExceeded => none
  | .evmReceive => none
  | .forBody _ body => body.findSome? (opEscapedArg limit)
  | .indexSetLeaf _ i v _ _ | .indexSet _ i v _ _ | .mapGetU64 i v =>
      #[i, v].findSome? (valEscapedArg limit)
  | .mapSetU64 a b c => #[a, b, c].findSome? (valEscapedArg limit)
  | .mapGetAddr a b c d => #[a, b, c, d].findSome? (valEscapedArg limit)
  | .mapSetAddr a b c d e => #[a, b, c, d, e].findSome? (valEscapedArg limit)
  | .mapGetPair a b c d e f g =>
      #[a, b, c, d, e, f, g].findSome? (valEscapedArg limit)
  | .mapSetPair a b c d e f g h =>
      #[a, b, c, d, e, f, g, h].findSome? (valEscapedArg limit)
  | .mapSetAddr256 a b c d e f g h =>
      #[a, b, c, d, e, f, g, h].findSome? (valEscapedArg limit)
  | .mapSetPair256 a b c d e f g h i j k =>
      #[a, b, c, d, e, f, g, h, i, j, k].findSome? (valEscapedArg limit)
  | .evmTokenTransfer a b c d e f g =>
      #[a, b, c, d, e, f, g].findSome? (valEscapedArg limit)
  | .evmTokenTransfer256 a b c d e f g h i j =>
      #[a, b, c, d, e, f, g, h, i, j].findSome? (valEscapedArg limit)
  | .evmTokenApprove256 a b c d e f g h i j =>
      #[a, b, c, d, e, f, g, h, i, j].findSome? (valEscapedArg limit)
  | .evmTokenTransferFrom256 a b c d e f g h i j k l m =>
      #[a, b, c, d, e, f, g, h, i, j, k, l, m].findSome? (valEscapedArg limit)
  | .evmTokenBalanceOfSelf a b c =>
      #[a, b, c].findSome? (valEscapedArg limit)
  | .evmWethDeposit256 a b c d0 d1 d2 d3 =>
      #[a, b, c, d0, d1, d2, d3].findSome? (valEscapedArg limit)
  | .evmWethWithdraw256 a b c d0 d1 d2 d3 =>
      #[a, b, c, d0, d1, d2, d3].findSome? (valEscapedArg limit)
  | .evmSwapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[r0, r1, r2, a0, a1, a2, b0, b1, b2, i0, i1, i2, i3, m0, m1, m2, m3].findSome?
        (valEscapedArg limit)
  | .evmSwapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[r0, r1, r2, a0, a1, a2, b0, b1, b2, c0, c1, c2, i0, i1, i2, i3, m0, m1, m2, m3].findSome?
        (valEscapedArg limit)
  | .evmPermit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      #[o0, o1, o2, s0, s1, s2, v0, v1, v2, v3, d0, d1, d2, d3, vv, r0, r1, r2, r3, z0, z1, z2, z3].findSome?
        (valEscapedArg limit)
  | .evmTokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      #[t0, t1, t2, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3, d0, d1, d2, d3, vv, r0, r1, r2, r3, z0, z1, z2, z3].findSome?
        (valEscapedArg limit)
  | .evmComponent call => call.values.findSome? (valEscapedArg limit)
  | .storeField _ v | .okState v | .returnU64 v | .returnState v => valEscapedArg limit v
  | .errorOverflow | .errorNamed _ => none
  | .errorTyped frame => frame.values.findSome? (valEscapedArg limit)

/-- Reject decoder binder leaks before a backend can mistake one for calldata or state. -/
private def checkArgBounds (p : IR.Program) : Except String Unit := do
  for method in p.methods do
    let limit := method.paramCount + if method.kind == .init then 0 else 1
    for op in method.ops do
      if let some i := opEscapedArg limit op then
        (throw (s!"extract/unsupported: {method.ixName} escaped arg {i} " ++
          s!"(paramCount {method.paramCount})") : Except String Unit)
  return ()

/-- Extract three named declarations directly into the extensible source dialect. -/
def extractProgramIR (env : Environment)
    (initName incrementName getName : Name)
    (programName : Option String := none)
    (fields? : Option (Array String) := none) :
    Except String IR.Program := do
  match Profile.checkAll env #[initName, incrementName, getName] with
  | .reject reason => throw reason
  | .accept => pure ()
  let schema ← inferSchema env initName
  let inferred := Core.IR.slotsOfSchema schema
  let slots ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred.map (·.name) then pure inferred
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred.map (·.name)}"
  let initM ← extractMethod env .init initName
  let incM ← extractMethod env .increment incrementName
  let getM ← extractMethod env .get getName
  let program : IR.Program := {
    name := programName.getD (programNameOfInit initName)
    slots
    schema
    methods := #[initM, incM, getM]
  }
  unless Core.IR.isProgramShape program do
    throw "extract/unsupported: not three-method shape"
  unless Core.IR.schemaMatchesSlots program do
    throw "extract/unsupported: schema does not match slots"
  checkInitCoverage program
  let program ← resolveVectorLeaves program
  checkArgBounds program
  let program ← evaluateProgram program
  checkUsedFields program
  return program

def extractCounterIR := extractProgramIR

private def isExceptType (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some ``Except

/-- `Except` → mutate；`UInt64` → view；其它用户 structure → init。
`UInt64` 本身也是 structure，必须先判。 -/
def inferKind (env : Environment) (n : Name) : Except String Core.IR.MethodKind := do
  let some info := env.find? n
    | throw s!"extract/unsupported: unknown {n}"
  let ret := peelForalls info.type
  if isExceptType ret then
    return .increment
  if isUInt64Type ret || (codecScalarOfType ret).isSome then
    return .get
  if ret.getAppFn.constName? == some ``Prod then
    return .get
  if ret.getAppFn.constName? == some boundedVecName ||
      ret.getAppFn.constName? == some boundedBytesName ||
      ret.getAppFn.constName? == some boundedStringName then
    return .get
  if let some typeName := ret.getAppFn.constName? then
    if !isStructure env typeName &&
        (match env.find? typeName with | some (.inductInfo _) => true | _ => false) then
      return .get
  if let some structName := ret.getAppFn.constName? then
    if Attr.isBoundary env structName then
      return .get
    if isStructure env structName && structName != ``UInt64 &&
        structName != ``Prod && structName != addr20Name &&
        structName != uint128Name && structName != uint256Name &&
        structName != fixedBytesName then
      return .init
  throw s!"extract/unsupported: cannot classify {n}"

private def sortNames (ns : Array Name) : Array Name :=
  ns.qsort (·.toString < ·.toString)

/-- 收同一名字空间下 `@[pf_entry]` 的根，直接生成 extensible IR。 -/
def extractModuleIR (env : Environment) (ns : Name)
    (fields? : Option (Array String) := none) :
    Except String IR.Program := do
  let tagged := sortNames (Attr.entriesIn env ns)
  if tagged.isEmpty then
    throw "extract/unsupported: no pf_entry"
  let mut inits : Array Name := #[]
  let mut muts : Array Name := #[]
  let mut views : Array Name := #[]
  for n in tagged do
    match Profile.check env n with
    | .reject reason => throw reason
    | .accept => pure ()
    match ← inferKind env n with
    | .init => inits := inits.push n
    | .increment => muts := muts.push n
    | .get => views := views.push n
  if inits.isEmpty then
    throw "extract/unsupported: missing init method"
  if muts.isEmpty then
    throw "extract/unsupported: missing mutating method"
  if views.isEmpty then
    throw "extract/unsupported: missing view method"
  let initName :=
    match inits.find? (fun n => Core.IR.lastName n.toString == "init") with
    | some n => n
    | none => inits[0]!
  let schema ← inferSchema env initName
  let inferred := Core.IR.slotsOfSchema schema
  let slots ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred.map (·.name) then pure inferred
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred.map (·.name)}"
  let mut methods : Array IR.Method := #[]
  let mut seen : Array String := #[]
  for n in inits do
    let m ←
      match extractMethod env .init n with
      | .ok method => pure method
      | .error reason => throw s!"{n}: {reason}"
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
  for n in muts do
    let m ←
      match extractMethod env .increment n with
      | .ok method => pure method
      | .error reason => throw s!"{n}: {reason}"
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
  for n in views do
    let m ←
      match extractMethod env .get n with
      | .ok method => pure method
      | .error reason => throw s!"{n}: {reason}"
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
  let program : IR.Program := {
    name := programNameOfInit initName
    slots
    schema
    methods
  }
  unless Core.IR.isProgramShape program do
    throw "extract/unsupported: not program shape"
  unless Core.IR.schemaMatchesSlots program do
    throw "extract/unsupported: schema does not match slots"
  checkInitCoverage program
  let program ← resolveVectorLeaves program
  checkArgBounds program
  let program ← evaluateProgram program
  checkUsedFields program
  return program

end ProofForge.Extract
