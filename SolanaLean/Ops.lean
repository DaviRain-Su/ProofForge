namespace SolanaLean.Ops

/-- v0 可发射操作。值是局部编号，由抽出器分配。 -/
inductive Val where
  /-- 方法参数，0 起。init 的 `initial`、increment 的 `s`/`delta`、get 的 `s`。 -/
  | arg (i : Nat)
  /-- 结构投影 `.value`。 -/
  | field (base : Val) (name : String)
  /-- 已检查的 `x + y`（前置条件已在 ite 真支）。 -/
  | add (x y : Val)
  /-- `u64Max - x`。 -/
  | subFromMax (x : Val)
  deriving BEq, Repr, Inhabited

inductive Op where
  /-- `if field ≤ u64Max - rhs` 然后真支 / 假支。 -/
  | checkedAddU64 (lhs rhs : Val)
  /-- 返回 `Except.ok (State.mk v, v)`。 -/
  | okState (value : Val)
  /-- 返回 `Except.error overflow`。 -/
  | errorOverflow
  /-- 返回裸 `UInt64`（view）。 -/
  | returnU64 (value : Val)
  /-- 返回 `State.mk v`（init）。 -/
  | returnState (value : Val)
  deriving BEq, Repr, Inhabited

def hasCheckedAdd (ops : Array Op) : Bool :=
  ops.any (fun
    | .checkedAddU64 .. => true
    | _ => false)

end SolanaLean.Ops
