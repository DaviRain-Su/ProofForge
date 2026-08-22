namespace SolanaLean.Ops

/-- 可 load 的值。`clockSlot` / `signerKey0` 是 SVM 叶子；`evmCaller` / `evmBlockNumber` 是 EVM 叶子。 -/
inductive Val where
  | arg (i : Nat)
  | field (base : Val) (name : String)
  | lit (n : UInt64)
  | clockSlot
  | signerKey0
  | evmCaller
  | evmBlockNumber
  | evmTimestamp
  | evmChainId
  | evmSelf
  | evmCallValue
  | evmSelfBalance
  | evmCallerW0 | evmCallerW1 | evmCallerW2
  | evmSelfW0 | evmSelfW1 | evmSelfW2
  | bitAnd (lhs rhs : Val)
  | bitOr (lhs rhs : Val)
  | bitXor (lhs rhs : Val)
  | bitNot (v : Val)
  | shiftL (lhs rhs : Val)
  | shiftR (lhs rhs : Val)
  | indexGet (base : Val) (name : String) (idx : Val) (len : Nat)
  | loopIx
  deriving BEq, Repr, Inhabited

inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving BEq, Repr, Inhabited, DecidableEq

inductive Op where
  | checkedAddU64 (lhs rhs : Val)
  | checkedSubU64 (lhs rhs : Val)
  | checkedMulU64 (lhs rhs : Val)
  | checkedDivU64 (lhs rhs : Val)
  | checkedModU64 (lhs rhs : Val)
  | ite (cmp : Cmp) (lhs rhs : Val) (thn els : Array Op)
  | systemTransfer (amount : Val)
  | evmDeposit (amount : Val)
  | evmSendEth (w0 w1 w2 amount : Val)
  | evmLogTipped (amount : Val)
  | forAccum (n : Nat) (addend : Val)
  | indexSet (name : String) (idx value : Val) (len : Nat)
  | okState (value : Val)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Val)
  | returnState (value : Val)
  deriving BEq, Repr, Inhabited

private def walk (fuel : Nat) (ops : Array Op) (p : Op → Bool) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun op =>
      p op ||
        match op with
        | .ite _ _ _ t f => walk fuel' t p || walk fuel' f p
        | _ => false

def hasEvmDeposit (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmDeposit _ => true | _ => false)

def hasEvmSendEth (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmSendEth .. => true | _ => false)

def hasEvmLog (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmLogTipped _ => true | _ => false)

def hasSystemTransfer (ops : Array Op) : Bool :=
  walk 16 ops (fun | .systemTransfer _ => true | _ => false)

def hasCheckedAdd (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedAddU64 .. => true | _ => false)

def hasCheckedSub (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedSubU64 .. => true | _ => false)

def hasCheckedMul (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedMulU64 .. => true | _ => false)

def hasCheckedDiv (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedDivU64 .. => true | _ => false)

def hasCheckedMod (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedModU64 .. => true | _ => false)

def hasCheckedArith (ops : Array Op) : Bool :=
  hasCheckedAdd ops || hasCheckedSub ops ||
    hasCheckedMul ops || hasCheckedDiv ops || hasCheckedMod ops

def isLangVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR ..
  | .indexGet .. | .loopIx => true
  | .field b _ => isLangVal b
  | _ => false

def isLangLeaf : Val → Bool
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      isLangLeaf l || isLangLeaf r
  | .bitNot v => isLangLeaf v
  | .indexGet b _ i _ => isLangLeaf b || isLangLeaf i
  | .loopIx => true
  | .field b _ => isLangLeaf b
  | _ => false

def isEvmLeaf : Val → Bool
  | .evmCaller | .evmBlockNumber | .evmTimestamp | .evmChainId
  | .evmSelf | .evmCallValue | .evmSelfBalance
  | .evmCallerW0 | .evmCallerW1 | .evmCallerW2
  | .evmSelfW0 | .evmSelfW1 | .evmSelfW2 => true
  | .field b _ => isEvmLeaf b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      isEvmLeaf l || isEvmLeaf r
  | .bitNot v => isEvmLeaf v
  | .indexGet b _ i _ => isEvmLeaf b || isEvmLeaf i
  | _ => false

def hasEvmLeaf (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .checkedAddU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedSubU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedMulU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedDivU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedModU64 l r => isEvmLeaf l || isEvmLeaf r
    | .ite _ l r _ _ => isEvmLeaf l || isEvmLeaf r
    | .systemTransfer v => isEvmLeaf v
    | .evmDeposit v => isEvmLeaf v
    | .evmSendEth a b c d =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d
    | .evmLogTipped v => isEvmLeaf v
    | .forAccum _ v => isEvmLeaf v
    | .indexSet _ i v _ => isEvmLeaf i || isEvmLeaf v
    | .okState v => isEvmLeaf v
    | .returnU64 v => isEvmLeaf v
    | .returnState v => isEvmLeaf v
    | .errorOverflow | .errorNamed _ => false

def hasLangLeaf (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .checkedAddU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedSubU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedMulU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedDivU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedModU64 l r => isLangLeaf l || isLangLeaf r
    | .ite _ l r _ _ => isLangLeaf l || isLangLeaf r
    | .systemTransfer v => isLangLeaf v
    | .evmDeposit v => isLangLeaf v
    | .evmSendEth a b c d =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d
    | .evmLogTipped v => isLangLeaf v
    | .forAccum _ v => isLangLeaf v
    | .indexSet _ i v _ => isLangLeaf i || isLangLeaf v
    | .okState v => isLangLeaf v
    | .returnU64 v => isLangLeaf v
    | .returnState v => isLangLeaf v
    | .errorOverflow | .errorNamed _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walk 16 ops (fun | .forAccum .. => true | _ => false)

def hasIndexSet (ops : Array Op) : Bool :=
  walk 16 ops (fun | .indexSet .. => true | _ => false)

def hasErrorNamed (ops : Array Op) : Bool :=
  walk 16 ops (fun | .errorNamed _ => true | _ => false)

def hasLangOp (ops : Array Op) : Bool :=
  hasForAccum ops || hasIndexSet ops || hasErrorNamed ops || hasLangLeaf ops

def hasEvmEffect (ops : Array Op) : Bool :=
  hasEvmDeposit ops || hasEvmSendEth ops || hasEvmLog ops || hasEvmLeaf ops

end SolanaLean.Ops
