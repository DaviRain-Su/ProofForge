import ProofForge.Core.Ops
import ProofForge.Core.IR
import ProofForge.Core.CFG
import ProofForge.Svm.Ops
import ProofForge.Evm.Ops
import ProofForge.Wasm.Xrpl.Ops
import ProofForge.Wasm.Near.Ops

namespace ProofForge.Extract.IR

/-- The extractor is the only layer that combines target-owned value extensions. -/
inductive ValKind where
  | svm (kind : Svm.Ops.ValKind)
  | evm (kind : Evm.Ops.ValKind)
  | xrpl (kind : Wasm.Xrpl.Ops.ValKind)
  | near (kind : ProofForge.Wasm.Near.Ops.ValKind)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .svm kind => kind.arity
  | .evm kind => kind.arity
  | .xrpl kind => kind.arity
  | .near kind => kind.arity

/-- Target effects stay strongly typed while sharing the extractor's recursive value type. -/
inductive OpExt (V : Type) where
  | svm (payload : Svm.Ops.OpExt V)
  | evm (payload : Evm.Ops.OpExt V)
  | xrpl (payload : Wasm.Xrpl.Ops.OpExt V)
  | near (payload : ProofForge.Wasm.Near.Ops.OpExt V)
  deriving BEq, Repr, Inhabited

abbrev Cmp := Core.Ops.Cmp
abbrev Val := Core.Ops.Val ValKind
abbrev Op := Core.Ops.Op ValKind OpExt
abbrev Evaluation := Core.Evaluation ValKind
abbrev Method := Core.IR.Method ValKind OpExt
abbrev Program := Core.IR.Program ValKind OpExt
abbrev CFG := Core.CFG.Graph ValKind OpExt

private def mapSvmPayload (mapValue : Val → Val) : Svm.Ops.OpExt Val → Svm.Ops.OpExt Val
  | .invoke programIx metas data seeds bump =>
      .invoke programIx metas (data.map (Svm.Ops.CpiWord.map mapValue)) seeds (bump.map mapValue)
  | .component call => .component (call.mapValues mapValue)

private def svmPayloadValues : Svm.Ops.OpExt Val → Array Val
  | .invoke _ _ data _ bump =>
      data.filterMap Svm.Ops.CpiWord.value? ++ match bump with
        | some value => #[value]
        | none => #[]
  | .component call => call.values

private def mapEvmPayload (mapValue : Val → Val) : Evm.Ops.OpExt Val → Evm.Ops.OpExt Val
  | .component call => .component (call.mapValues mapValue)

private def evmPayloadValues : Evm.Ops.OpExt Val → Array Val
  | .component call => call.values

private def mapXrplPayload (_mapValue : Val → Val) : Wasm.Xrpl.Ops.OpExt Val → Wasm.Xrpl.Ops.OpExt Val
  | .reserved => .reserved

private def xrplPayloadValues : Wasm.Xrpl.Ops.OpExt Val → Array Val
  | .reserved => #[]

def OpExt.mapValues (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .svm payload => .svm (mapSvmPayload mapValue payload)
  | .evm payload => .evm (mapEvmPayload mapValue payload)
  | .xrpl payload => .xrpl (mapXrplPayload mapValue payload)
  | .near payload =>
      match payload with
      | .reserved => .near .reserved

def OpExt.values : OpExt Val → Array Val
  | .svm payload => svmPayloadValues payload
  | .evm payload => evmPayloadValues payload
  | .xrpl payload => xrplPayloadValues payload
  | .near _ => #[]

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := OpExt.mapValues
  values := OpExt.values
  payloadEq := fun left right => left == right

/-- Build and optimize the shared target-neutral CFG for one extracted method. -/
def toCFG (ops : Array Op) : Except String CFG := do
  let graph ← Core.CFG.lower cfgDialect ops
  Core.CFG.optimize cfgDialect graph

def methodToCFG (method : Method) : Except String CFG := do
  let graph ←
    if method.kind == .init then Core.CFG.lowerInit cfgDialect method.ops
    else Core.CFG.lower cfgDialect method.ops
  Core.CFG.optimize cfgDialect graph

private def svmExtWellFormed : Svm.Ops.OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.all (fun word => word.value?.all (·.wellFormed ValKind.arity)) &&
      match bump with
      | some value => value.wellFormed ValKind.arity
      | none => true
  | .component call =>
      call.wellFormed (·.wellFormed ValKind.arity) Svm.Ops.maxTxAccountLocks

private def evmExtWellFormed : Evm.Ops.OpExt Val → Bool
  | .component call => call.wellFormed (·.wellFormed ValKind.arity)

private def xrplExtWellFormed : Wasm.Xrpl.Ops.OpExt Val → Bool
  | .reserved => false

def OpExt.wellFormed : OpExt Val → Bool
  | .svm payload => svmExtWellFormed payload
  | .evm payload => evmExtWellFormed payload
  | .xrpl payload => xrplExtWellFormed payload
  | .near payload =>
      match payload with
      | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
