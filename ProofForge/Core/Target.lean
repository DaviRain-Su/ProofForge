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
  | .errorTyped frame =>
      return .errorTyped (← frame.mapValuesM (projectVal registration))
  | .returnU64 value => return .returnU64 (← projectVal registration value)
  | .returnState value => return .returnState (← projectVal registration value)
  | .ext payload =>
      return .ext (← registration.projectOpExt (projectVal registration) payload)

def projectOps (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (ops : Array (Core.Ops.Op SrcValExt SrcOpExt)) :
    Except String (Array (Core.Ops.Op ValExt OpExt)) :=
  ops.mapM (projectOp registration)

/-- Root-first, fallible rewrite for a target lowering pass. Returning `some` replaces a complete
subtree; returning `none` delegates recursion to Core. This keeps target adapters focused on the
boundary values they own instead of duplicating the common value AST traversal. -/
partial def rewriteValRoots
    (rewriteRoot : Core.Ops.Val ValExt → Except String (Option (Core.Ops.Val ValExt))) :
    Core.Ops.Val ValExt → Except String (Core.Ops.Val ValExt)
  | value => do
      if let some rewritten ← rewriteRoot value then
        return rewritten
      match value with
      | .arg i => pure (.arg i)
      | .local i => pure (.local i)
      | .field base name => return .field (← rewriteValRoots rewriteRoot base) name
      | .lit n => pure (.lit n)
      | .bitAnd lhs rhs =>
          return .bitAnd (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .bitOr lhs rhs =>
          return .bitOr (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .bitXor lhs rhs =>
          return .bitXor (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .bitNot inner => return .bitNot (← rewriteValRoots rewriteRoot inner)
      | .shiftL lhs rhs =>
          return .shiftL (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .shiftR lhs rhs =>
          return .shiftR (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .indexGet base name index len elemOffset =>
          return .indexGet (← rewriteValRoots rewriteRoot base) name
            (← rewriteValRoots rewriteRoot index) len elemOffset
      | .loopIx => pure .loopIx
      | .select cmp lhs rhs thenValue elseValue =>
          return .select cmp (← rewriteValRoots rewriteRoot lhs)
            (← rewriteValRoots rewriteRoot rhs) (← rewriteValRoots rewriteRoot thenValue)
            (← rewriteValRoots rewriteRoot elseValue)
      | .addU64 lhs rhs =>
          return .addU64 (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .subU64 lhs rhs =>
          return .subU64 (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .mulU64 lhs rhs =>
          return .mulU64 (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .divU64 lhs rhs =>
          return .divU64 (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .modU64 lhs rhs =>
          return .modU64 (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
      | .ext kind operands =>
          return .ext kind (← operands.mapM (rewriteValRoots rewriteRoot))

/-- Rewrite every common value in an operation while delegating an opaque target payload to its
owner. Nested control flow is traversed once here for all targets. -/
partial def rewriteOpValues
    (rewriteRoot : Core.Ops.Val ValExt → Except String (Option (Core.Ops.Val ValExt)))
    (rewritePayload :
      (Core.Ops.Val ValExt → Except String (Core.Ops.Val ValExt)) →
      OpExt (Core.Ops.Val ValExt) → Except String (OpExt (Core.Ops.Val ValExt))) :
    Core.Ops.Op ValExt OpExt → Except String (Core.Ops.Op ValExt OpExt)
  | .letLocal i value => return .letLocal i (← rewriteValRoots rewriteRoot value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => return .setLocal i (← rewriteValRoots rewriteRoot value)
  | .checkedAddU64 lhs rhs =>
      return .checkedAddU64 (← rewriteValRoots rewriteRoot lhs)
        (← rewriteValRoots rewriteRoot rhs)
  | .checkedSubU64 lhs rhs =>
      return .checkedSubU64 (← rewriteValRoots rewriteRoot lhs)
        (← rewriteValRoots rewriteRoot rhs)
  | .checkedMulU64 lhs rhs =>
      return .checkedMulU64 (← rewriteValRoots rewriteRoot lhs)
        (← rewriteValRoots rewriteRoot rhs)
  | .checkedDivU64 lhs rhs =>
      return .checkedDivU64 (← rewriteValRoots rewriteRoot lhs)
        (← rewriteValRoots rewriteRoot rhs)
  | .checkedModU64 lhs rhs =>
      return .checkedModU64 (← rewriteValRoots rewriteRoot lhs)
        (← rewriteValRoots rewriteRoot rhs)
  | .ite cmp lhs rhs thenOps elseOps =>
      return .ite cmp (← rewriteValRoots rewriteRoot lhs) (← rewriteValRoots rewriteRoot rhs)
        (← thenOps.mapM (rewriteOpValues rewriteRoot rewritePayload))
        (← elseOps.mapM (rewriteOpValues rewriteRoot rewritePayload))
  | .forAccum bound addend resultLocal =>
      return .forAccum bound (← rewriteValRoots rewriteRoot addend) resultLocal
  | .forBody bound body =>
      return .forBody bound (← body.mapM (rewriteOpValues rewriteRoot rewritePayload))
  | .indexSetLeaf name index value len leaf =>
      return .indexSetLeaf name (← rewriteValRoots rewriteRoot index)
        (← rewriteValRoots rewriteRoot value) len leaf
  | .indexSet name index value len elemOffset =>
      return .indexSet name (← rewriteValRoots rewriteRoot index)
        (← rewriteValRoots rewriteRoot value) len elemOffset
  | .storeField name value => return .storeField name (← rewriteValRoots rewriteRoot value)
  | .okState value => return .okState (← rewriteValRoots rewriteRoot value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .errorTyped frame =>
      return .errorTyped (← frame.mapValuesM (rewriteValRoots rewriteRoot))
  | .returnU64 value => return .returnU64 (← rewriteValRoots rewriteRoot value)
  | .returnState value => return .returnState (← rewriteValRoots rewriteRoot value)
  | .ext payload =>
      return .ext (← rewritePayload (rewriteValRoots rewriteRoot) payload)

def rewriteOpsValues
    (rewriteRoot : Core.Ops.Val ValExt → Except String (Option (Core.Ops.Val ValExt)))
    (rewritePayload :
      (Core.Ops.Val ValExt → Except String (Core.Ops.Val ValExt)) →
      OpExt (Core.Ops.Val ValExt) → Except String (OpExt (Core.Ops.Val ValExt)))
    (ops : Array (Core.Ops.Op ValExt OpExt)) : Except String (Array (Core.Ops.Op ValExt OpExt)) :=
  ops.mapM (rewriteOpValues rewriteRoot rewritePayload)

private def validateCFG [BEq ValExt]
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (kind : Core.IR.MethodKind) (ops : Array (Core.Ops.Op ValExt OpExt)) :
    Except String Unit := do
  let graph ←
    if kind == .init then Core.CFG.lowerInit registration.cfgDialect ops
    else Core.CFG.lower registration.cfgDialect ops
  let _ ← Core.CFG.optimize registration.cfgDialect graph
  pure ()

private def validateBoundarySchemas (method : Core.IR.Method SrcValExt SrcOpExt) :
    Except String Unit := do
  unless method.paramSchemas.isEmpty do
    unless method.paramSchemas.size == method.paramCount do
      throw s!"extract/unsupported: {method.ixName} boundary parameter schema count mismatch"
    for schema in method.paramSchemas do
      match Core.Codec.validate schema with
      | .ok _ => pure ()
      | .error reason => throw s!"extract/unsupported: {method.ixName}: {reason}"
  match Core.Codec.validate method.retSchema with
  | .ok _ => pure ()
  | .error reason => throw s!"extract/unsupported: {method.ixName}: {reason}"

def projectMethod [BEq ValExt]
    (registration : Registration SrcValExt SrcOpExt ValExt OpExt)
    (schema : Core.Schema) (method : Core.IR.Method SrcValExt SrcOpExt) :
    Except String (Core.IR.Method ValExt OpExt) := do
  validateBoundarySchemas method
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
    paramTypes := method.paramTypes
    paramSchemas := method.paramSchemas
    retWidths := method.retWidths
    retTypes := method.retTypes
    retSchema := method.retSchema
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
