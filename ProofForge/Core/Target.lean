import ProofForge.Core.IR
import ProofForge.Core.CFG

namespace ProofForge.Core.Target

/--
A statically registered projection from one source dialect to one target dialect. Common Core
values and operations are projected generically; a target owns only the two extension callbacks,
its validation contract, and the CFG dialect consumed by its backend.
-/
structure Registration (SrcValExt : Type) (SrcOpExt : Type → Type)
    (ValExt : Type) (OpExt : Type → Type) where
  name : String
  projectValExt : SrcValExt → Except String ValExt
  projectOpExt :
    (Core.Ops.Val SrcValExt → Except String (Core.Ops.Val ValExt)) →
    SrcOpExt (Core.Ops.Val SrcValExt) →
    Except String (OpExt (Core.Ops.Val ValExt))
  projectionError : String → String → String := fun _ reason => reason
  valArity : ValExt → Nat
  opWellFormed : Core.Ops.Op ValExt OpExt → Bool
  cfgDialect : Core.CFG.Dialect ValExt OpExt

partial def projectVal
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt) :
    Core.Ops.Val SrcValExt → Except String (Core.Ops.Val ValExt)
  | .arg i => pure (.arg i)
  | .local i => pure (.local i)
  | .field base name => return .field (← projectVal registration base) name
  | .lit n => pure (.lit n)
  | .bitAnd lhs rhs =>
      return .bitAnd (← projectVal registration lhs) (← projectVal registration rhs)
  | .bitOr lhs rhs =>
      return .bitOr (← projectVal registration lhs) (← projectVal registration rhs)
  | .bitXor lhs rhs =>
      return .bitXor (← projectVal registration lhs) (← projectVal registration rhs)
  | .bitNot value => return .bitNot (← projectVal registration value)
  | .shiftL lhs rhs =>
      return .shiftL (← projectVal registration lhs) (← projectVal registration rhs)
  | .shiftR lhs rhs =>
      return .shiftR (← projectVal registration lhs) (← projectVal registration rhs)
  | .indexGet base name index len elemOffset =>
      return .indexGet (← projectVal registration base) name
        (← projectVal registration index) len elemOffset
  | .loopIx => pure .loopIx
  | .select cmp lhs rhs thenValue elseValue =>
      return .select cmp (← projectVal registration lhs) (← projectVal registration rhs)
        (← projectVal registration thenValue) (← projectVal registration elseValue)
  | .addU64 lhs rhs =>
      return .addU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .subU64 lhs rhs =>
      return .subU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .mulU64 lhs rhs =>
      return .mulU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .divU64 lhs rhs =>
      return .divU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .modU64 lhs rhs =>
      return .modU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .ext kind operands => do
      let targetKind ← registration.projectValExt kind
      let targetOperands ← operands.mapM (projectVal registration)
      unless targetOperands.size == registration.valArity targetKind do
        throw s!"extract/ir: malformed {registration.name} value extension"
      return .ext targetKind targetOperands

partial def projectOp
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt) :
    Core.Ops.Op SrcValExt SrcOpExt → Except String (Core.Ops.Op ValExt OpExt)
  | .letLocal i value => return .letLocal i (← projectVal registration value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => return .setLocal i (← projectVal registration value)
  | .checkedAddU64 lhs rhs =>
      return .checkedAddU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .checkedSubU64 lhs rhs =>
      return .checkedSubU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .checkedMulU64 lhs rhs =>
      return .checkedMulU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .checkedDivU64 lhs rhs =>
      return .checkedDivU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .checkedModU64 lhs rhs =>
      return .checkedModU64 (← projectVal registration lhs) (← projectVal registration rhs)
  | .ite cmp lhs rhs thenOps elseOps =>
      return .ite cmp (← projectVal registration lhs) (← projectVal registration rhs)
        (← thenOps.mapM (projectOp registration)) (← elseOps.mapM (projectOp registration))
  | .forAccum bound addend resultLocal =>
      return .forAccum bound (← projectVal registration addend) resultLocal
  | .forBody bound body =>
      return .forBody bound (← body.mapM (projectOp registration))
  | .indexSetLeaf name index value len leaf =>
      return .indexSetLeaf name (← projectVal registration index)
        (← projectVal registration value) len leaf
  | .indexSet name index value len elemOffset =>
      return .indexSet name (← projectVal registration index)
        (← projectVal registration value) len elemOffset
  | .storeField name value => return .storeField name (← projectVal registration value)
  | .okState value => return .okState (← projectVal registration value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => return .returnU64 (← projectVal registration value)
  | .returnState value => return .returnState (← projectVal registration value)
  | .ext payload =>
      return .ext (← registration.projectOpExt (projectVal registration) payload)

def projectOps (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (ops : Array (Core.Ops.Op SrcValExt SrcOpExt)) :
    Except String (Array (Core.Ops.Op ValExt OpExt)) :=
  ops.mapM (projectOp registration)

private def validateCFG [BEq ValExt]
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (kind : Core.IR.MethodKind) (ops : Array (Core.Ops.Op ValExt OpExt)) :
    Except String Unit := do
  let graph ←
    if kind == .init then Core.CFG.lowerInit registration.cfgDialect ops
    else Core.CFG.lower registration.cfgDialect ops
  let _ ← Core.CFG.optimize registration.cfgDialect graph
  pure ()

def projectMethod [BEq ValExt]
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (schema : Core.Schema) (method : Core.IR.Method SrcValExt SrcOpExt) :
    Except String (Core.IR.Method ValExt OpExt) := do
  let ops ←
    match projectOps registration method.ops with
    | .ok ops => pure ops
    | .error reason => throw (registration.projectionError method.ixName reason)
  unless ops.all registration.opWellFormed do
    throw s!"extract/ir: malformed {registration.name} Ops in {method.ixName}"
  match validateCFG registration method.kind ops with
  | .ok _ => pure ()
  | .error reason => throw s!"extract/cfg: {method.ixName}: {reason}"
  let evaluation ←
    if schema.isEmpty then pure {}
    else Core.evaluate schema ops
  return {
    kind := method.kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    retWidths := method.retWidths
    retCount := method.retCount
    annotations := method.annotations
    sketch := method.sketch
    ops
    evaluation
  }

/--
Project and validate a source program using one target-owned registration. Adding a backend that
accepts the existing Core language only requires a new registration; this function and the source
dialect remain unchanged.
-/
def projectProgram [BEq ValExt]
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (program : Core.IR.Program SrcValExt SrcOpExt) :
    Except String (Core.IR.Program ValExt OpExt) := do
  return {
    name := program.name
    slots := program.slots
    schema := program.schema
    methods := ← program.methods.mapM (projectMethod registration program.schema)
  }

end ProofForge.Core.Target
