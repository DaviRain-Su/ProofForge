import ProofForge.Evm.Component
import ProofForge.Evm.Ops
import ProofForge.Evm.HashedMap.Emit
import ProofForge.Evm.WideWord.Emit

namespace ProofForge.Evm.Component.Emit

/-- Generic component emission context. Component backends share value materialization and
fresh-name / wide-cache state; the main emitter supplies this record once. -/
structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
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

def emitCall (context : Context σ) (call : Component.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) :=
  match call with
  | .empty => .error "extract/unsupported: evm empty component call"
  | .hashedMap storageCall =>
      HashedMap.Emit.emitCall context.hashedMap storageCall st

end ProofForge.Evm.Component.Emit
