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
  | okState (value : Val)
  | errorOverflow
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

def isEvmLeaf : Val → Bool
  | .evmCaller | .evmBlockNumber | .evmTimestamp | .evmChainId
  | .evmSelf | .evmCallValue | .evmSelfBalance
  | .evmCallerW0 | .evmCallerW1 | .evmCallerW2
  | .evmSelfW0 | .evmSelfW1 | .evmSelfW2 => true
  | .field b _ => isEvmLeaf b
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
    | .okState v => isEvmLeaf v
    | .returnU64 v => isEvmLeaf v
    | .returnState v => isEvmLeaf v
    | .errorOverflow => false

def hasEvmEffect (ops : Array Op) : Bool :=
  hasEvmDeposit ops || hasEvmSendEth ops || hasEvmLog ops || hasEvmLeaf ops

end SolanaLean.Ops
