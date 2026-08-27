import ProofForge.Core.Ops
import ProofForge.Evm.Component

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
  | immU64
  | immU64b
  | immW0 | immW1 | immW2
  | immX0 | immX1 | immX2
  /-- packed `callvalue()` limb; `limb` is 0..3 (w0 lowest). -/
  | callValue256 (limb : Nat)
  /-- packed `selfbalance()` limb; `limb` is 0..3 (w0 lowest). -/
  | selfBalance256 (limb : Nat)
  /-- EIP-712 domain separator limb; `limb` is 0..3 (w0 lowest). -/
  | domainSep256 (limb : Nat)
  /-- Bounded EVM component query. New value vocabularies extend `Component.Query`. -/
  | component (query : Component.Query)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .callValue256 _ | .selfBalance256 _ | .domainSep256 _ => 0
  | .component query => query.arity
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- EVM-only source effects. -/
inductive OpExt (V : Type) where
  | deposit (amount : V)
  | deposit256 (a0 a1 a2 a3 : V)
  | sendEth (w0 w1 w2 amount : V)
  | sendEth256 (w0 w1 w2 a0 a1 a2 a3 : V)
  | log (name : String) (amount : V)
  | logTransfer256 (f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 : V)
  | logApproval256 (o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 : V)
  | revertInsufficient (h0 h1 h2 h3 w0 w1 w2 w3 : V)
  | revertUnauthorized (w0 w1 w2 : V)
  | revertZeroAddress
  | receive
  /-- Bounded EVM component effect. New effect vocabularies extend `Component.Call`. -/
  | component (call : Component.Call V)
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
def immU64 : Val := leaf .immU64
def immU64b : Val := leaf .immU64b
def immW0 : Val := leaf .immW0
def immW1 : Val := leaf .immW1
def immW2 : Val := leaf .immW2
def immX0 : Val := leaf .immX0
def immX1 : Val := leaf .immX1
def immX2 : Val := leaf .immX2
def mapGetU64 (base key : Val) : Val :=
  .ext (.component (.hashedMap .getU64)) #[base, key]
def mapGetAddr (base w0 w1 w2 : Val) : Val :=
  .ext (.component (.hashedMap .getAddr)) #[base, w0, w1, w2]
def mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.component (.hashedMap .getPair)) #[base, o0, o1, o2, s0, s1, s2]
def mapGetAddr256 (limb : Nat) (base w0 w1 w2 : Val) : Val :=
  .ext (.component (.hashedMap (.getAddr256 limb))) #[base, w0, w1, w2]
def mapGetPair256 (limb : Nat) (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.component (.hashedMap (.getPair256 limb))) #[base, o0, o1, o2, s0, s1, s2]
def tokenBalance256 (limb : Nat) (tw0 tw1 tw2 : Val) : Val :=
  .ext (.component (.closedCall (.balance256 limb))) #[tw0, tw1, tw2]
def tokenAllowance256 (limb : Nat) (tw0 tw1 tw2 o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.component (.closedCall (.allowance256 limb))) #[tw0, tw1, tw2, o0, o1, o2, s0, s1, s2]
def callValue256 (limb : Nat) : Val := .ext (.callValue256 limb) #[]
def selfBalance256 (limb : Nat) : Val := .ext (.selfBalance256 limb) #[]
def domainSep256 (limb : Nat) : Val := .ext (.domainSep256 limb) #[]
def ge256 (a0 a1 a2 a3 b0 b1 b2 b3 : Val) : Val :=
  .ext (.component (.wideWord .ge256)) #[a0, a1, a2, a3, b0, b1, b2, b3]
def eq20 (a0 a1 a2 b0 b1 b2 : Val) : Val :=
  .ext (.component (.wideWord .eq20)) #[a0, a1, a2, b0, b1, b2]
def arith256 (op limb : Nat) (a0 a1 a2 a3 b0 b1 b2 b3 : Val) : Val :=
  .ext (.component (.wideWord (.arith256 op limb))) #[a0, a1, a2, a3, b0, b1, b2, b3]

private def allValuesWellFormed (values : Array Val) : Bool :=
  values.all (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .deposit amount | .log _ amount => allValuesWellFormed #[amount]
  | .deposit256 a0 a1 a2 a3 => allValuesWellFormed #[a0, a1, a2, a3]
  | .sendEth w0 w1 w2 amount => allValuesWellFormed #[w0, w1, w2, amount]
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      allValuesWellFormed #[w0, w1, w2, a0, a1, a2, a3]
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      allValuesWellFormed #[f0, f1, f2, t0, t1, t2, a0, a1, a2, a3]
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      allValuesWellFormed #[o0, o1, o2, s0, s1, s2, a0, a1, a2, a3]
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      allValuesWellFormed #[h0, h1, h2, h3, w0, w1, w2, w3]
  | .revertUnauthorized w0 w1 w2 => allValuesWellFormed #[w0, w1, w2]
  | .revertZeroAddress => true
  | .receive => true
  | .component call => call.wellFormed (·.wellFormed ValKind.arity)

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Evm.Ops
