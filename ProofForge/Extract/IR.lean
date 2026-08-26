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
  | .mapSetAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      .mapSetAddr256 (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)
  | .mapSetPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      .mapSetPair256 (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      .tokenTransfer (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2) (mapValue amount)
  | .tokenTransfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      .tokenTransfer256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .tokenApprove256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      .tokenApprove256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue sw0) (mapValue sw1) (mapValue sw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .tokenTransferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      .tokenTransferFrom256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue ow0) (mapValue ow1) (mapValue ow2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .tokenBalanceOfSelf tw0 tw1 tw2 =>
      .tokenBalanceOfSelf (mapValue tw0) (mapValue tw1) (mapValue tw2)
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      .wethDeposit256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      .wethWithdraw256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      .swapExact2 (mapValue rw0) (mapValue rw1) (mapValue rw2)
        (mapValue a0) (mapValue a1) (mapValue a2)
        (mapValue b0) (mapValue b1) (mapValue b2)
        (mapValue i0) (mapValue i1) (mapValue i2) (mapValue i3)
        (mapValue m0) (mapValue m1) (mapValue m2) (mapValue m3)

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
  | .mapGetU64 base key => #[base, key]
  | .mapSetU64 base key value => #[base, key, value]
  | .mapGetAddr base w0 w1 w2 => #[base, w0, w1, w2]
  | .mapSetAddr base w0 w1 w2 value => #[base, w0, w1, w2, value]
  | .mapGetPair base o0 o1 o2 s0 s1 s2 => #[base, o0, o1, o2, s0, s1, s2]
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value => #[base, o0, o1, o2, s0, s1, s2, value]
  | .mapSetAddr256 base w0 w1 w2 v0 v1 v2 v3 => #[base, w0, w1, w2, v0, v1, v2, v3]
  | .mapSetPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      #[base, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3]
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount => #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
  | .tokenTransfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .tokenApprove256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, sw0, sw1, sw2, a0, a1, a2, a3]
  | .tokenTransferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, ow0, ow1, ow2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .tokenBalanceOfSelf tw0 tw1 tw2 => #[tw0, tw1, tw2]
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, a0, a1, a2, a3]
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, a0, a1, a2, a3]
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[rw0, rw1, rw2, a0, a1, a2, b0, b1, b2, i0, i1, i2, i3, m0, m1, m2, m3]

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
  | .mapGetU64 base key => #[base, key].all (·.wellFormed ValKind.arity)
  | .mapSetU64 base key value => #[base, key, value].all (·.wellFormed ValKind.arity)
  | .mapGetAddr base w0 w1 w2 => #[base, w0, w1, w2].all (·.wellFormed ValKind.arity)
  | .mapSetAddr base w0 w1 w2 value =>
      #[base, w0, w1, w2, value].all (·.wellFormed ValKind.arity)
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      #[base, o0, o1, o2, s0, s1, s2].all (·.wellFormed ValKind.arity)
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      #[base, o0, o1, o2, s0, s1, s2, value].all (·.wellFormed ValKind.arity)
  | .mapSetAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      #[base, w0, w1, w2, v0, v1, v2, v3].all (·.wellFormed ValKind.arity)
  | .mapSetPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      #[base, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3].all (·.wellFormed ValKind.arity)
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, amount].all (·.wellFormed ValKind.arity)
  | .tokenTransfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .tokenApprove256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, sw0, sw1, sw2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .tokenTransferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, ow0, ow1, ow2, dw0, dw1, dw2, a0, a1, a2, a3].all
        (·.wellFormed ValKind.arity)
  | .tokenBalanceOfSelf tw0 tw1 tw2 =>
      #[tw0, tw1, tw2].all (·.wellFormed ValKind.arity)
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, a0, a1, a2, a3].all (·.wellFormed ValKind.arity)
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[rw0, rw1, rw2, a0, a1, a2, b0, b1, b2, i0, i1, i2, i3, m0, m1, m2, m3].all
        (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .svm payload => svmExtWellFormed payload
  | .evm payload => evmExtWellFormed payload

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
