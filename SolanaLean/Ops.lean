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

private def isEvmLeaf : Val → Bool
  | .evmCaller | .evmBlockNumber => true
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
    | .okState v => isEvmLeaf v
    | .returnU64 v => isEvmLeaf v
    | .returnState v => isEvmLeaf v
    | .errorOverflow => false

end SolanaLean.Ops
