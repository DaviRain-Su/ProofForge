import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Wasm.Ops

/-!
# WASM target IR

Static registration of the extractor-to-WASM projection plus the physical program shape
consumed by `ProofForge.Wasm.Emit`. v0 binds the WASM slice to XRPL Bedrock (XLS-0101):
the artifact is a scaffold-xrp-dialect Rust source, the host contract is
`xrpl_wasm_std` `get_data`/`set_data`, and the canonical digest domain is
`wasm-xrpl|` — deliberately distinct from the SVM and EVM domains.

v0 subset (fail closed on everything else):

- state: `UInt64` leaves only (slot width 8), read through `read_u64`/written through
  `write_u64` on the contract pseudo-account;
- params: scalar `UInt64` only; public view results: exactly one `UInt64` returned
  through the FFI-safe `-> u64` export ABI; mutating entries return an `i32` status
  code only;
- ops: checked `+ - * / %`, `ite`, `okState`/`returnState`/`returnU64`,
  `errorOverflow`, `storeField`. Loops, locals, vectors, maps, named errors, and all
  svm/evm extensions are rejected;
- no host capability leaves: ledger time / caller account / hashing stay absent until
  their XRPL wasm-level import ABI is pinned.
-/

namespace ProofForge.Wasm.IR

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .svm _ => throw "extract/unsupported: wasm rejects svm value"
  | .evm _ => throw "extract/unsupported: wasm rejects evm value"

private def projectOpExt
    (_projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .svm _ => throw "extract/unsupported: wasm rejects svm effect"
  | .evm _ => throw "extract/unsupported: wasm rejects evm effect"

/-- Static registration of the extractor-to-WASM projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt where
  name := "WASM"
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun method reason =>
    if reason.startsWith "extract/unsupported: wasm rejects" then
      s!"{reason} in {method}"
    else reason
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := Ops.cfgDialect

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

/-- One lowered method. `tupleArity = some _` marks an infallible `-> u64` view;
`none` selects the `-> i32` status ABI (initializer and mutating entries).
`echoDropped` records that the source also declared a public result value which the v0
status ABI does not carry on-chain. -/
structure Method where
  kind : Core.IR.MethodKind
  name : String
  ixName : String
  paramCount : Nat := 0
  tupleArity : Option Nat := none
  echoDropped : Bool := false
  ops : Array Ops.Op := #[]
  evaluation : Core.Evaluation Ops.ValKind := {}
  deriving Inhabited

structure Program where
  name : String
  slots : Array Core.IR.Slot
  initializer : Method
  entries : Array Method
  deriving Inhabited

def slotNames (p : Program) : Array String :=
  p.slots.map (·.name)

/-! ## v0 subset checks -/

/-- Values the v0 Rust renderer can express. Guard computations rely on wrapping
two's-complement `+ - *`; unchecked `/ %` is rejected because Rust panics (traps) on
divide-by-zero outside the checked path. -/
private partial def valAllowed : Ops.Val → Bool
  | .arg _ | .lit _ => true
  | .field (.arg _) _ => true
  | .select _ lhs rhs thn els =>
      valAllowed lhs && valAllowed rhs && valAllowed thn && valAllowed els
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs =>
      valAllowed lhs && valAllowed rhs
  | _ => false

/-- Ops the v0 Rust renderer can express. -/
private partial def opAllowed : Ops.Op → Bool
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valAllowed lhs && valAllowed rhs
  | .ite _ lhs rhs thn els =>
      valAllowed lhs && valAllowed rhs && thn.all opAllowed && els.all opAllowed
  | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
      valAllowed value
  | .errorOverflow => true
  | _ => false

/-- Views are infallible on-chain reads: any checked or error op is rejected. -/
private partial def hasFallible (ops : Array Ops.Op) : Bool :=
  ops.any fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. | .errorOverflow | .errorNamed _ => true
    | .ite _ _ _ thn els => hasFallible thn || hasFallible els
    | _ => false

private def isScalarU64 : Core.Codec.Schema → Bool
  | .scalar (.uint 64) => true
  | _ => false

private def checkParams (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String Unit := do
  unless method.paramSchemas.all isScalarU64 do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"
  unless method.paramWidths.isEmpty || method.paramWidths.all (· == 8) do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"
  unless method.paramTypes.isEmpty || method.paramTypes.all (· == .uint 64) do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"

private def checkViewReturn (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String Unit := do
  unless method.retTypes.isEmpty || method.retTypes.all (· == .uint 64) do
    throw s!"extract/unsupported: {method.ixName} wants a UInt64 view result for wasm v0"
  unless method.retWidths.isEmpty || method.retWidths.all (· == 8) do
    throw s!"extract/unsupported: {method.ixName} wants a UInt64 view result for wasm v0"
  unless method.retCount == 1 do
    throw s!"extract/unsupported: {method.ixName} view result count {method.retCount} is out of range; wasm v0 wants exactly one"

/-- Project the combined extractor dialect and lower it into a WASM-owned physical program. -/
def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  for method in src.methods do
    unless method.annotations.isEmpty do
      throw s!"extract/unsupported: wasm cannot consume target annotations on {method.ixName}"
  let source ← Core.Target.projectProgram extractRegistration src
  if source.slots.isEmpty then
    throw "extract/unsupported: wasm program has no slots"
  for slot in source.slots do
    unless slot.width == 8 do
      throw s!"extract/unsupported: wasm v0 wants UInt64 state {slot.name}, got width {slot.width}"
  let mut initializer? : Option (Core.IR.Method Ops.ValKind Ops.OpExt) := none
  let mut sources : Array (Core.IR.Method Ops.ValKind Ops.OpExt) := #[]
  for method in source.methods do
    checkParams method
    unless method.ops.all opAllowed do
      throw s!"extract/unsupported: {method.ixName} uses an op outside the wasm v0 subset"
    if method.kind == .init then
      if initializer?.isSome then
        throw "extract/unsupported: wasm wants exactly one initializer"
      unless method.ops.any (fun | .returnState _ => true | _ => false) do
        throw "extract/unsupported: wasm init missing returnState"
      initializer? := some method
    else
      sources := sources.push method
  let some initSrc := initializer? | throw "extract/unsupported: wasm wants an initializer"
  if sources.isEmpty then
    throw "extract/unsupported: wasm wants at least one entry"
  let init : Method := {
    kind := initSrc.kind
    name := initSrc.name
    ixName := initSrc.ixName
    paramCount := initSrc.paramCount
    tupleArity := none
    ops := initSrc.ops
    evaluation := initSrc.evaluation
  }
  let mut entries : Array Method := #[]
  for m in sources do
    if m.kind == .get then
      checkViewReturn m
      if hasFallible m.ops then
        throw s!"extract/unsupported: {m.ixName} view must be infallible for wasm v0"
    let tupleArity := if m.kind == .get then some m.retCount else none
    let echoDropped := m.kind != .get && !m.retTypes.isEmpty
    entries := entries.push {
      kind := m.kind
      name := m.name
      ixName := m.ixName
      paramCount := m.paramCount
      tupleArity
      echoDropped
      ops := m.ops
      evaluation := m.evaluation
    }
  return {
    name := source.name
    slots := source.slots
    initializer := init
    entries
  }

/-! ## Canonical digest

Domain `wasm-xrpl|` is pinned and deliberately different from the SVM / EVM domains:
the host ABI norm differs, so artifacts must never be conflated across targets.
-/

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

private partial def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field base name => s!"f.{name}({valCanon base})"
  | .bitAnd lhs rhs => s!"and({valCanon lhs},{valCanon rhs})"
  | .bitOr lhs rhs => s!"or({valCanon lhs},{valCanon rhs})"
  | .bitXor lhs rhs => s!"xor({valCanon lhs},{valCanon rhs})"
  | .bitNot value => s!"not({valCanon value})"
  | .shiftL lhs rhs => s!"shl({valCanon lhs},{valCanon rhs})"
  | .shiftR lhs rhs => s!"shr({valCanon lhs},{valCanon rhs})"
  | .indexGet base name idx len off =>
      s!"idx.{name}[{valCanon idx}/{len}+{off}]({valCanon base})"
  | .loopIx => "ix"
  | .select cmp lhs rhs thn els =>
      s!"sel.{cmpTag cmp}({valCanon lhs},{valCanon rhs},{valCanon thn},{valCanon els})"
  | .addU64 lhs rhs => s!"uadd({valCanon lhs},{valCanon rhs})"
  | .subU64 lhs rhs => s!"usub({valCanon lhs},{valCanon rhs})"
  | .mulU64 lhs rhs => s!"umul({valCanon lhs},{valCanon rhs})"
  | .divU64 lhs rhs => s!"udiv({valCanon lhs},{valCanon rhs})"
  | .modU64 lhs rhs => s!"umod({valCanon lhs},{valCanon rhs})"
  | .ext _ operands =>
      s!"wext({String.intercalate "," (operands.map valCanon).toList})"

private partial def opsCanon (ops : Array Ops.Op) : String :=
  let rec one (op : Ops.Op) : String :=
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
    | .forAccum n value resultLocal => s!"for.{resultLocal}({n},{valCanon value})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSetLeaf name idx value len leaf =>
        s!"isetl.{name}.{leaf}[{valCanon idx}/{len}]({valCanon value})"
    | .indexSet name idx value len elemOff =>
        s!"iset.{name}+{elemOff}[{valCanon idx}/{len}]({valCanon value})"
    | .storeField name value => s!"st.{name}({valCanon value})"
    | .okState value => s!"ok({valCanon value})"
    | .errorOverflow => "ovf"
    | .errorNamed name => s!"err.{name}"
    | .returnU64 value => s!"retu({valCanon value})"
    | .returnState value => s!"rets({valCanon value})"
    | .ext _ => "wext"
  String.intercalate ";" (ops.toList.map one)

private def methodCanon (method : Method) : String :=
  let tag := match method.tupleArity with
    | some n => s!"view{n}"
    | none => "mut"
  let echo := if method.echoDropped then "echo" else "noecho"
  s!"{tag}:{method.ixName}:{method.paramCount}:{echo}:[{opsCanon method.ops}]"

def canonical (p : Program) : String :=
  let slots := String.intercalate ","
    (p.slots.map (fun s => s!"{s.name}:{s.width}")).toList
  let entries :=
    (p.entries.qsort (fun a b => a.ixName < b.ixName)).toList.map methodCanon
  s!"wasm-xrpl|{p.name}|{slots}|{methodCanon p.initializer}|{String.intercalate "/" entries}"

def digestHex (p : Program) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical p))

end ProofForge.Wasm.IR