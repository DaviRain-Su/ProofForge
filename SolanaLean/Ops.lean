namespace SolanaLean.Ops

/-- 可 load 的值。 -/
inductive Val where
  | arg (i : Nat)
  | field (base : Val) (name : String)
  | lit (n : UInt64)
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

end SolanaLean.Ops
