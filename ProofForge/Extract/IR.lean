import ProofForge.Core.Ops
import ProofForge.Core.IR
import ProofForge.Core.CFG
import ProofForge.Svm.Ops
import ProofForge.Evm.Ops

namespace ProofForge.Extract.IR

/-- The extractor is the only layer that combines target-owned value extensions. -/
inductive ValKind where
  | svm (kind : Svm.Ops.ValKind)
  | evm (kind : Evm.Ops.ValKind)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .svm kind => kind.arity
  | .evm kind => kind.arity

/-- Target effects stay strongly typed while sharing the extractor's recursive value type. -/
inductive OpExt (V : Type) where
  | svm (payload : Svm.Ops.OpExt V)
  | evm (payload : Evm.Ops.OpExt V)
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

private def svmPayloadValues : Svm.Ops.OpExt Val → Array Val
  | .invoke _ _ data _ bump =>
      data.filterMap Svm.Ops.CpiWord.value? ++ match bump with
        | some value => #[value]
        | none => #[]

private def mapEvmPayload (mapValue : Val → Val) : Evm.Ops.OpExt Val → Evm.Ops.OpExt Val
  | .deposit amount => .deposit (mapValue amount)
  | .sendEth w0 w1 w2 amount => .sendEth (mapValue w0) (mapValue w1) (mapValue w2)
      (mapValue amount)
  | .log name amount => .log name (mapValue amount)
  | .mapGetU64 base key => .mapGetU64 (mapValue base) (mapValue key)
  | .mapSetU64 base key value => .mapSetU64 (mapValue base) (mapValue key) (mapValue value)
  | .mapGetAddr base w0 w1 w2 =>
      .mapGetAddr (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2)
  | .mapSetAddr base w0 w1 w2 value =>
      .mapSetAddr (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2) (mapValue value)
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      .mapGetPair (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      .mapSetPair (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2) (mapValue value)
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      .tokenTransfer (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2) (mapValue amount)
  | .tokenBalanceOfSelf tw0 tw1 tw2 =>
      .tokenBalanceOfSelf (mapValue tw0) (mapValue tw1) (mapValue tw2)

private def evmPayloadValues : Evm.Ops.OpExt Val → Array Val
  | .deposit amount | .log _ amount => #[amount]
  | .sendEth w0 w1 w2 amount => #[w0, w1, w2, amount]
  | .mapGetU64 base key => #[base, key]
  | .mapSetU64 base key value => #[base, key, value]
  | .mapGetAddr base w0 w1 w2 => #[base, w0, w1, w2]
  | .mapSetAddr base w0 w1 w2 value => #[base, w0, w1, w2, value]
  | .mapGetPair base o0 o1 o2 s0 s1 s2 => #[base, o0, o1, o2, s0, s1, s2]
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value => #[base, o0, o1, o2, s0, s1, s2, value]
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount => #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
  | .tokenBalanceOfSelf tw0 tw1 tw2 => #[tw0, tw1, tw2]

def OpExt.mapValues (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .svm payload => .svm (mapSvmPayload mapValue payload)
  | .evm payload => .evm (mapEvmPayload mapValue payload)

def OpExt.values : OpExt Val → Array Val
  | .svm payload => svmPayloadValues payload
  | .evm payload => evmPayloadValues payload

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

private def evmExtWellFormed : Evm.Ops.OpExt Val → Bool
  | .deposit amount | .log _ amount => amount.wellFormed ValKind.arity
  | .sendEth w0 w1 w2 amount =>
      #[w0, w1, w2, amount].all (·.wellFormed ValKind.arity)
  | .mapGetU64 base key => #[base, key].all (·.wellFormed ValKind.arity)
  | .mapSetU64 base key value => #[base, key, value].all (·.wellFormed ValKind.arity)
  | .mapGetAddr base w0 w1 w2 => #[base, w0, w1, w2].all (·.wellFormed ValKind.arity)
  | .mapSetAddr base w0 w1 w2 value =>
      #[base, w0, w1, w2, value].all (·.wellFormed ValKind.arity)
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      #[base, o0, o1, o2, s0, s1, s2].all (·.wellFormed ValKind.arity)
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      #[base, o0, o1, o2, s0, s1, s2, value].all (·.wellFormed ValKind.arity)
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, amount].all (·.wellFormed ValKind.arity)
  | .tokenBalanceOfSelf tw0 tw1 tw2 =>
      #[tw0, tw1, tw2].all (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .svm payload => svmExtWellFormed payload
  | .evm payload => evmExtWellFormed payload

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
