import ProofForge.Core.Ops

namespace ProofForge.Evm.Ops

/-- EVM-only source value intrinsics. Recursive operands live in `Core.Ops.Val.ext`. -/
inductive ValKind where
  | caller
  | blockNumber
  | timestamp
  | chainId
  | self
  | callValue
  | selfBalance
  | callerW0 | callerW1 | callerW2
  | selfW0 | selfW1 | selfW2
  | mapGetU64
  | mapGetAddr
  | mapGetPair
  /-- Checked 256-bit `add`/`sub`/`mul`; `limb` is 0..3 (w0 lowest). Eight operands: a0..a3, b0..b3. -/
  | arith256 (op : Nat) (limb : Nat)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .mapGetU64 => 2
  | .mapGetAddr => 4
  | .mapGetPair => 7
  | .arith256 _ _ => 8
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- EVM-only source effects. -/
inductive OpExt (V : Type) where
  | deposit (amount : V)
  | sendEth (w0 w1 w2 amount : V)
  | log (name : String) (amount : V)
  | mapGetU64 (base key : V)
  | mapSetU64 (base key value : V)
  | mapGetAddr (base w0 w1 w2 : V)
  | mapSetAddr (base w0 w1 w2 value : V)
  | mapGetPair (base o0 o1 o2 s0 s1 s2 : V)
  | mapSetPair (base o0 o1 o2 s0 s1 s2 value : V)
  | tokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : V)
  | tokenBalanceOfSelf (tw0 tw1 tw2 : V)
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

private def leaf (kind : ValKind) : Val := .ext kind #[]

def caller : Val := leaf .caller
def blockNumber : Val := leaf .blockNumber
def timestamp : Val := leaf .timestamp
def chainId : Val := leaf .chainId
def self : Val := leaf .self
def callValue : Val := leaf .callValue
def selfBalance : Val := leaf .selfBalance
def callerW0 : Val := leaf .callerW0
def callerW1 : Val := leaf .callerW1
def callerW2 : Val := leaf .callerW2
def selfW0 : Val := leaf .selfW0
def selfW1 : Val := leaf .selfW1
def selfW2 : Val := leaf .selfW2
def mapGetU64 (base key : Val) : Val := .ext .mapGetU64 #[base, key]
def mapGetAddr (base w0 w1 w2 : Val) : Val := .ext .mapGetAddr #[base, w0, w1, w2]
def mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext .mapGetPair #[base, o0, o1, o2, s0, s1, s2]
def arith256 (op limb : Nat) (a0 a1 a2 a3 b0 b1 b2 b3 : Val) : Val :=
  .ext (.arith256 op limb) #[a0, a1, a2, a3, b0, b1, b2, b3]

private def allValuesWellFormed (values : Array Val) : Bool :=
  values.all (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .deposit amount | .log _ amount => allValuesWellFormed #[amount]
  | .sendEth w0 w1 w2 amount => allValuesWellFormed #[w0, w1, w2, amount]
  | .mapGetU64 base key => allValuesWellFormed #[base, key]
  | .mapSetU64 base key value => allValuesWellFormed #[base, key, value]
  | .mapGetAddr base w0 w1 w2 => allValuesWellFormed #[base, w0, w1, w2]
  | .mapSetAddr base w0 w1 w2 value => allValuesWellFormed #[base, w0, w1, w2, value]
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      allValuesWellFormed #[base, o0, o1, o2, s0, s1, s2]
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      allValuesWellFormed #[base, o0, o1, o2, s0, s1, s2, value]
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      allValuesWellFormed #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
  | .tokenBalanceOfSelf tw0 tw1 tw2 => allValuesWellFormed #[tw0, tw1, tw2]

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Evm.Ops
