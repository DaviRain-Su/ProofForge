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
  | .component call => .component (call.mapValues mapValue)

private def svmPayloadValues : Svm.Ops.OpExt Val → Array Val
  | .invoke _ _ data _ bump =>
      data.filterMap Svm.Ops.CpiWord.value? ++ match bump with
        | some value => #[value]
        | none => #[]
  | .component call => call.values

private def mapEvmPayload (mapValue : Val → Val) : Evm.Ops.OpExt Val → Evm.Ops.OpExt Val
  | .deposit amount => .deposit (mapValue amount)
  | .deposit256 a0 a1 a2 a3 =>
      .deposit256 (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .sendEth w0 w1 w2 amount => .sendEth (mapValue w0) (mapValue w1) (mapValue w2)
      (mapValue amount)
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      .sendEth256 (mapValue w0) (mapValue w1) (mapValue w2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .log name amount => .log name (mapValue amount)
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      .logTransfer256 (mapValue f0) (mapValue f1) (mapValue f2)
        (mapValue t0) (mapValue t1) (mapValue t2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      .logApproval256 (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      .revertInsufficient (mapValue h0) (mapValue h1) (mapValue h2) (mapValue h3)
        (mapValue w0) (mapValue w1) (mapValue w2) (mapValue w3)
  | .revertUnauthorized w0 w1 w2 =>
      .revertUnauthorized (mapValue w0) (mapValue w1) (mapValue w2)
  | .revertZeroAddress => .revertZeroAddress
  | .receive => .receive
  | .component call => .component (call.mapValues mapValue)

private def evmPayloadValues : Evm.Ops.OpExt Val → Array Val
  | .deposit amount | .log _ amount => #[amount]
  | .deposit256 a0 a1 a2 a3 => #[a0, a1, a2, a3]
  | .sendEth w0 w1 w2 amount => #[w0, w1, w2, amount]
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 => #[w0, w1, w2, a0, a1, a2, a3]
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      #[f0, f1, f2, t0, t1, t2, a0, a1, a2, a3]
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      #[o0, o1, o2, s0, s1, s2, a0, a1, a2, a3]
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      #[h0, h1, h2, h3, w0, w1, w2, w3]
  | .revertUnauthorized w0 w1 w2 => #[w0, w1, w2]
  | .revertZeroAddress => #[]
  | .receive => #[]
  | .component call => call.values

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
  | .component call =>
      call.wellFormed (·.wellFormed ValKind.arity) Svm.Ops.maxTxAccountLocks

private def evmExtWellFormed : Evm.Ops.OpExt Val → Bool
  | .deposit amount | .log _ amount => amount.wellFormed ValKind.arity
  | .deposit256 a0 a1 a2 a3 =>
      #[a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .sendEth w0 w1 w2 amount =>
      #[w0, w1, w2, amount].all (·.wellFormed ValKind.arity)
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      #[w0, w1, w2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      #[f0, f1, f2, t0, t1, t2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      #[o0, o1, o2, s0, s1, s2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      #[h0, h1, h2, h3, w0, w1, w2, w3].all (·.wellFormed ValKind.arity)
  | .revertUnauthorized w0 w1 w2 =>
      #[w0, w1, w2].all (·.wellFormed ValKind.arity)
  | .revertZeroAddress => true
  | .receive => true
  | .component call => call.wellFormed (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .svm payload => svmExtWellFormed payload
  | .evm payload => evmExtWellFormed payload

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
