import ProofForge.Evm.Component
import ProofForge.Evm.Ops
import ProofForge.Evm.HashedMap.Emit
import ProofForge.Evm.WideWord.Emit
import ProofForge.Evm.ClosedCall.Emit
import ProofForge.Evm.NativeFx.Emit
import ProofForge.Evm.StaticStorage.Emit
import ProofForge.Evm.Environment.Emit

namespace ProofForge.Evm.Component.Emit

/-- Generic component emission context. Component backends share value materialization and
fresh-name / wide-cache state; the main emitter supplies this record once. -/
structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
  resolveStaticU64Slot : String → Except String Nat := fun field =>
    .error s!"extract/unsupported: no static UInt64 resolver for {field}"
  indent : String

private def Context.hashedMap (context : Context σ) : HashedMap.Emit.Context σ :=
  { materialize := context.materialize
    fresh := context.fresh
    rememberWide := context.rememberWide
    lookupWide := context.lookupWide
    valKey := context.valKey
    indent := context.indent }

private def Context.wideWord (context : Context σ) : WideWord.Emit.Context σ :=
  { materialize := context.materialize
    fresh := context.fresh
    rememberWide := context.rememberWide
    lookupWide := context.lookupWide
    valKey := context.valKey
    indent := context.indent }

private def Context.closedCall (context : Context σ) : ClosedCall.Emit.Context σ :=
  { materialize := context.materialize
    fresh := context.fresh
    rememberWide := context.rememberWide
    lookupWide := context.lookupWide
    valKey := context.valKey
    indent := context.indent }

private def Context.nativeFx (context : Context σ) : NativeFx.Emit.Context σ :=
  { materialize := context.materialize
    fresh := context.fresh
    indent := context.indent }

private def Context.staticStorage (context : Context σ) : StaticStorage.Emit.Context σ :=
  { materialize := context.materialize
    resolveU64Slot := context.resolveStaticU64Slot
    indent := context.indent }

private def Context.environment (context : Context σ) : Environment.Emit.Context σ :=
  { fresh := context.fresh
    rememberWide := context.rememberWide
    lookupWide := context.lookupWide
    indent := context.indent }

def emitQuery (context : Context σ) (query : Component.Query) (operands : Array Ops.Val)
    (st : σ) : Except String (String × String × σ) :=
  match query with
  | .empty =>
      if operands.isEmpty then
        .error "extract/unsupported: evm empty component query"
      else
        .error "extract/unsupported: evm empty component query arity"
  | .hashedMap storageQuery =>
      HashedMap.Emit.emitQuery context.hashedMap storageQuery operands st
  | .wideWord wideQuery =>
      WideWord.Emit.emitQuery context.wideWord wideQuery operands st
  | .closedCall callQuery =>
      ClosedCall.Emit.emitQuery context.closedCall callQuery operands st
  | .environment environmentQuery =>
      Environment.Emit.emitQuery context.environment environmentQuery operands st

def emitCall (context : Context σ) (call : Component.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) :=
  match call with
  | .empty => .error "extract/unsupported: evm empty component call"
  | .hashedMap storageCall =>
      HashedMap.Emit.emitCall context.hashedMap storageCall st
  | .closedCall callCall =>
      ClosedCall.Emit.emitCall context.closedCall callCall st
  | .nativeFx fxCall =>
      NativeFx.Emit.emitCall context.nativeFx fxCall st
  | .staticStorage storageCall =>
      StaticStorage.Emit.emitCall context.staticStorage storageCall st

end ProofForge.Evm.Component.Emit
