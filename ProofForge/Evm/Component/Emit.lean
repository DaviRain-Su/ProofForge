import ProofForge.Evm.Component
import ProofForge.Evm.Ops

namespace ProofForge.Evm.Component.Emit

/-- Generic component emission context. Component backends share value loading; the main emitter
supplies this record once and remains independent of individual component constructors. -/
structure Context where
  loadValue : Ops.Val → Except String String

def emitQuery (_context : Context) (query : Component.Query) (operands : Array Ops.Val) :
    Except String String :=
  match query with
  | .empty =>
      if operands.isEmpty then
        .error "extract/unsupported: evm empty component query"
      else
        .error "extract/unsupported: evm empty component query arity"

def emitCall (_context : Context) : Component.Call Ops.Val → Except String String
  | .empty => .error "extract/unsupported: evm empty component call"

end ProofForge.Evm.Component.Emit
