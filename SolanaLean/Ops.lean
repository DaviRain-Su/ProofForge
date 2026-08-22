namespace SolanaLean.Ops

/-- 可 load 的值。 -/
inductive Val where
  | arg (i : Nat)
  | field (base : Val) (name : String)
  | lit (n : UInt64)
  deriving BEq, Repr, Inhabited

inductive Op where
  | checkedAddU64 (lhs rhs : Val)
  | checkedSubU64 (lhs rhs : Val)
  | okState (value : Val)
  | errorOverflow
  | returnU64 (value : Val)
  | returnState (value : Val)
  deriving BEq, Repr, Inhabited

def hasCheckedAdd (ops : Array Op) : Bool :=
  ops.any (fun | .checkedAddU64 .. => true | _ => false)

def hasCheckedSub (ops : Array Op) : Bool :=
  ops.any (fun | .checkedSubU64 .. => true | _ => false)

def hasCheckedArith (ops : Array Op) : Bool :=
  hasCheckedAdd ops || hasCheckedSub ops

end SolanaLean.Ops
