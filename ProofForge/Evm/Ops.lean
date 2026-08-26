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
  /-- 256-bit hashed map payload limb; `limb` is 0..3 (w0 lowest). -/
  | mapGetAddr256 (limb : Nat)
  | mapGetPair256 (limb : Nat)
  | tokenBalance256 (limb : Nat)
  /-- 256-bit ERC-20 `allowance` limb; nine operands: token, owner, spender. -/
  | tokenAllowance256 (limb : Nat)
  /-- packed `callvalue()` limb; `limb` is 0..3 (w0 lowest). -/
  | callValue256 (limb : Nat)
  /-- packed `selfbalance()` limb; `limb` is 0..3 (w0 lowest). -/
  | selfBalance256 (limb : Nat)
  /-- `a ≥ b` on packed 256-bit words. Eight operands: a0..a3, b0..b3. -/
  | ge256
  /-- Checked 256-bit `add`/`sub`/`mul`; `limb` is 0..3 (w0 lowest). Eight operands: a0..a3, b0..b3. -/
  | arith256 (op : Nat) (limb : Nat)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .mapGetU64 => 2
  | .mapGetAddr => 4
  | .mapGetPair => 7
  | .mapGetAddr256 _ => 4
  | .mapGetPair256 _ => 7
  | .tokenBalance256 _ => 3
  | .tokenAllowance256 _ => 9
  | .callValue256 _ | .selfBalance256 _ => 0
  | .ge256 => 8
  | .arith256 _ _ => 8
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
  | receive
  | mapGetU64 (base key : V)
  | mapSetU64 (base key value : V)
  | mapGetAddr (base w0 w1 w2 : V)
  | mapSetAddr (base w0 w1 w2 value : V)
  | mapGetPair (base o0 o1 o2 s0 s1 s2 : V)
  | mapSetPair (base o0 o1 o2 s0 s1 s2 value : V)
  | mapSetAddr256 (base w0 w1 w2 v0 v1 v2 v3 : V)
  | mapSetPair256 (base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 : V)
  | tokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : V)
  | tokenTransfer256 (tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 : V)
  | tokenApprove256 (tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 : V)
  | tokenTransferFrom256 (tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 : V)
  | tokenBalanceOfSelf (tw0 tw1 tw2 : V)
  | wethDeposit256 (tw0 tw1 tw2 a0 a1 a2 a3 : V)
  | wethWithdraw256 (tw0 tw1 tw2 a0 a1 a2 a3 : V)
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
def mapGetAddr256 (limb : Nat) (base w0 w1 w2 : Val) : Val :=
  .ext (.mapGetAddr256 limb) #[base, w0, w1, w2]
def mapGetPair256 (limb : Nat) (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.mapGetPair256 limb) #[base, o0, o1, o2, s0, s1, s2]
def tokenBalance256 (limb : Nat) (tw0 tw1 tw2 : Val) : Val :=
  .ext (.tokenBalance256 limb) #[tw0, tw1, tw2]
def tokenAllowance256 (limb : Nat) (tw0 tw1 tw2 o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.tokenAllowance256 limb) #[tw0, tw1, tw2, o0, o1, o2, s0, s1, s2]
def callValue256 (limb : Nat) : Val := .ext (.callValue256 limb) #[]
def selfBalance256 (limb : Nat) : Val := .ext (.selfBalance256 limb) #[]
def ge256 (a0 a1 a2 a3 b0 b1 b2 b3 : Val) : Val :=
  .ext .ge256 #[a0, a1, a2, a3, b0, b1, b2, b3]
def arith256 (op limb : Nat) (a0 a1 a2 a3 b0 b1 b2 b3 : Val) : Val :=
  .ext (.arith256 op limb) #[a0, a1, a2, a3, b0, b1, b2, b3]

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
  | .receive => true
  | .mapGetU64 base key => allValuesWellFormed #[base, key]
  | .mapSetU64 base key value => allValuesWellFormed #[base, key, value]
  | .mapGetAddr base w0 w1 w2 => allValuesWellFormed #[base, w0, w1, w2]
  | .mapSetAddr base w0 w1 w2 value => allValuesWellFormed #[base, w0, w1, w2, value]
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      allValuesWellFormed #[base, o0, o1, o2, s0, s1, s2]
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      allValuesWellFormed #[base, o0, o1, o2, s0, s1, s2, value]
  | .mapSetAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      allValuesWellFormed #[base, w0, w1, w2, v0, v1, v2, v3]
  | .mapSetPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      allValuesWellFormed #[base, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3]
  | .tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      allValuesWellFormed #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
  | .tokenTransfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      allValuesWellFormed #[tw0, tw1, tw2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .tokenApprove256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      allValuesWellFormed #[tw0, tw1, tw2, sw0, sw1, sw2, a0, a1, a2, a3]
  | .tokenTransferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      allValuesWellFormed #[tw0, tw1, tw2, ow0, ow1, ow2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .tokenBalanceOfSelf tw0 tw1 tw2 => allValuesWellFormed #[tw0, tw1, tw2]
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      allValuesWellFormed #[tw0, tw1, tw2, a0, a1, a2, a3]
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      allValuesWellFormed #[tw0, tw1, tw2, a0, a1, a2, a3]

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Evm.Ops
