import ProofForge.Core.Ops
import ProofForge.Core.IR
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

private def svmExtWellFormed : Svm.Ops.OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.all (fun
        | .u64le value => value.wellFormed ValKind.arity
        | _ => true) &&
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

private def rejectEvmValue : Except String α :=
  .error "extract/unsupported: svm rejects evm value"

partial def toSvmVal : Val → Except String Svm.Ops.Val
  | .arg i => pure (.arg i)
  | .local i => pure (.local i)
  | .field base name => return .field (← toSvmVal base) name
  | .lit n => pure (.lit n)
  | .bitAnd lhs rhs => return .bitAnd (← toSvmVal lhs) (← toSvmVal rhs)
  | .bitOr lhs rhs => return .bitOr (← toSvmVal lhs) (← toSvmVal rhs)
  | .bitXor lhs rhs => return .bitXor (← toSvmVal lhs) (← toSvmVal rhs)
  | .bitNot value => return .bitNot (← toSvmVal value)
  | .shiftL lhs rhs => return .shiftL (← toSvmVal lhs) (← toSvmVal rhs)
  | .shiftR lhs rhs => return .shiftR (← toSvmVal lhs) (← toSvmVal rhs)
  | .indexGet base name idx len elemOff =>
      return .indexGet (← toSvmVal base) name (← toSvmVal idx) len elemOff
  | .loopIx => pure .loopIx
  | .select cmp lhs rhs thn els =>
      return .select cmp (← toSvmVal lhs) (← toSvmVal rhs)
        (← toSvmVal thn) (← toSvmVal els)
  | .addU64 lhs rhs => return .addU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .subU64 lhs rhs => return .subU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .mulU64 lhs rhs => return .mulU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .divU64 lhs rhs => return .divU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .modU64 lhs rhs => return .modU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .ext (.svm kind) operands => return .ext kind (← operands.mapM toSvmVal)
  | .ext (.evm _) _ => rejectEvmValue

private def cpiWordToSvm : Svm.Ops.CpiWord Val → Except String (Svm.Ops.CpiWord Svm.Ops.Val)
  | .u8le n => pure (.u8le n)
  | .u32le n => pure (.u32le n)
  | .u64le value => return .u64le (← toSvmVal value)
  | .ascii value => pure (.ascii value)
  | .programId => pure .programId
  | .accKey i => pure (.accKey i)

partial def toSvmOp : Op → Except String Svm.Ops.Op
  | .letLocal i value => return .letLocal i (← toSvmVal value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => return .setLocal i (← toSvmVal value)
  | .checkedAddU64 lhs rhs => return .checkedAddU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .checkedSubU64 lhs rhs => return .checkedSubU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .checkedMulU64 lhs rhs => return .checkedMulU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .checkedDivU64 lhs rhs => return .checkedDivU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .checkedModU64 lhs rhs => return .checkedModU64 (← toSvmVal lhs) (← toSvmVal rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp (← toSvmVal lhs) (← toSvmVal rhs)
        (← thn.mapM toSvmOp) (← els.mapM toSvmOp)
  | .forAccum n addend => return .forAccum n (← toSvmVal addend)
  | .forBody n body => return .forBody n (← body.mapM toSvmOp)
  | .indexSetLeaf name _ _ _ leaf =>
      throw s!"extract/ir: unresolved vector leaf {name}.{leaf}"
  | .indexSet name idx value len elemOff =>
      return .indexSet name (← toSvmVal idx) (← toSvmVal value) len elemOff
  | .storeField name value => return .storeField name (← toSvmVal value)
  | .okState value => return .okState (← toSvmVal value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => return .returnU64 (← toSvmVal value)
  | .returnState value => return .returnState (← toSvmVal value)
  | .ext (.svm (.invoke programIx metas data seed bump)) =>
      return .ext (.invoke programIx metas (← data.mapM cpiWordToSvm)
        seed (← bump.mapM toSvmVal))
  | .ext (.evm _) => throw "extract/unsupported: svm rejects evm effect"

def toSvmOps (ops : Array Op) : Except String (Array Svm.Ops.Op) :=
  ops.mapM toSvmOp

private def rejectSvmValue : Except String α :=
  .error "extract/unsupported: evm rejects svm value"

partial def toEvmVal : Val → Except String Evm.Ops.Val
  | .arg i => pure (.arg i)
  | .local i => pure (.local i)
  | .field base name => return .field (← toEvmVal base) name
  | .lit n => pure (.lit n)
  | .bitAnd lhs rhs => return .bitAnd (← toEvmVal lhs) (← toEvmVal rhs)
  | .bitOr lhs rhs => return .bitOr (← toEvmVal lhs) (← toEvmVal rhs)
  | .bitXor lhs rhs => return .bitXor (← toEvmVal lhs) (← toEvmVal rhs)
  | .bitNot value => return .bitNot (← toEvmVal value)
  | .shiftL lhs rhs => return .shiftL (← toEvmVal lhs) (← toEvmVal rhs)
  | .shiftR lhs rhs => return .shiftR (← toEvmVal lhs) (← toEvmVal rhs)
  | .indexGet base name idx len elemOff =>
      return .indexGet (← toEvmVal base) name (← toEvmVal idx) len elemOff
  | .loopIx => pure .loopIx
  | .select cmp lhs rhs thn els =>
      return .select cmp (← toEvmVal lhs) (← toEvmVal rhs)
        (← toEvmVal thn) (← toEvmVal els)
  | .addU64 lhs rhs => return .addU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .subU64 lhs rhs => return .subU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .mulU64 lhs rhs => return .mulU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .divU64 lhs rhs => return .divU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .modU64 lhs rhs => return .modU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .ext (.evm kind) operands => return .ext kind (← operands.mapM toEvmVal)
  | .ext (.svm _) _ => rejectSvmValue

private def mapEvmValues (values : Array Val) : Except String (Array Evm.Ops.Val) :=
  values.mapM toEvmVal

partial def toEvmOp : Op → Except String Evm.Ops.Op
  | .letLocal i value => return .letLocal i (← toEvmVal value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => return .setLocal i (← toEvmVal value)
  | .checkedAddU64 lhs rhs => return .checkedAddU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .checkedSubU64 lhs rhs => return .checkedSubU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .checkedMulU64 lhs rhs => return .checkedMulU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .checkedDivU64 lhs rhs => return .checkedDivU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .checkedModU64 lhs rhs => return .checkedModU64 (← toEvmVal lhs) (← toEvmVal rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp (← toEvmVal lhs) (← toEvmVal rhs)
        (← thn.mapM toEvmOp) (← els.mapM toEvmOp)
  | .forAccum n addend => return .forAccum n (← toEvmVal addend)
  | .forBody n body => return .forBody n (← body.mapM toEvmOp)
  | .indexSetLeaf name _ _ _ leaf =>
      throw s!"extract/ir: unresolved vector leaf {name}.{leaf}"
  | .indexSet name idx value len elemOff =>
      return .indexSet name (← toEvmVal idx) (← toEvmVal value) len elemOff
  | .storeField name value => return .storeField name (← toEvmVal value)
  | .okState value => return .okState (← toEvmVal value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => return .returnU64 (← toEvmVal value)
  | .returnState value => return .returnState (← toEvmVal value)
  | .ext (.svm _) => throw "extract/unsupported: evm rejects svm effect"
  | .ext (.evm payload) =>
      match payload with
      | .deposit amount => return .ext (.deposit (← toEvmVal amount))
      | .sendEth w0 w1 w2 amount => do
          let values ← mapEvmValues #[w0, w1, w2, amount]
          return .ext (.sendEth values[0]! values[1]! values[2]! values[3]!)
      | .log name amount => return .ext (.log name (← toEvmVal amount))
      | .mapGetU64 base key => return .ext (.mapGetU64 (← toEvmVal base) (← toEvmVal key))
      | .mapSetU64 base key value =>
          return .ext (.mapSetU64 (← toEvmVal base) (← toEvmVal key) (← toEvmVal value))
      | .mapGetAddr base w0 w1 w2 => do
          let values ← mapEvmValues #[base, w0, w1, w2]
          return .ext (.mapGetAddr values[0]! values[1]! values[2]! values[3]!)
      | .mapSetAddr base w0 w1 w2 value => do
          let values ← mapEvmValues #[base, w0, w1, w2, value]
          return .ext (.mapSetAddr values[0]! values[1]! values[2]! values[3]! values[4]!)
      | .mapGetPair base o0 o1 o2 s0 s1 s2 => do
          let values ← mapEvmValues #[base, o0, o1, o2, s0, s1, s2]
          return .ext (.mapGetPair values[0]! values[1]! values[2]! values[3]!
            values[4]! values[5]! values[6]!)
      | .mapSetPair base o0 o1 o2 s0 s1 s2 value => do
          let values ← mapEvmValues #[base, o0, o1, o2, s0, s1, s2, value]
          return .ext (.mapSetPair values[0]! values[1]! values[2]! values[3]!
            values[4]! values[5]! values[6]! values[7]!)
      | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount => do
          let values ← mapEvmValues #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
          return .ext (.tokenTransfer values[0]! values[1]! values[2]! values[3]!
            values[4]! values[5]! values[6]!)
      | .tokenBalanceOfSelf tw0 tw1 tw2 => do
          let values ← mapEvmValues #[tw0, tw1, tw2]
          return .ext (.tokenBalanceOfSelf values[0]! values[1]! values[2]!)

def toEvmOps (ops : Array Op) : Except String (Array Evm.Ops.Op) :=
  ops.mapM toEvmOp

def Program.validateSvm (program : Program) : Except String Unit := do
  for method in program.methods do
    let ops ←
      match toSvmOps method.ops with
      | .ok ops => pure ops
      | .error _ => throw "extract/unsupported: svm rejects evm leaf"
    unless ops.all Svm.Ops.Op.wellFormed do
      throw s!"extract/ir: malformed SVM Ops in {method.ixName}"

def Program.validateEvm (program : Program) : Except String Unit := do
  for method in program.methods do
    let ops ←
      match toEvmOps method.ops with
      | .ok ops => pure ops
      | .error _ => throw s!"extract/unsupported: evm rejects svm leaf in {method.ixName}"
    unless ops.all Evm.Ops.Op.wellFormed do
      throw s!"extract/ir: malformed EVM Ops in {method.ixName}"

end ProofForge.Extract.IR
