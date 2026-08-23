import ProofForge

/-!
Sokoban 红黑树节点 + 定长 `Vector`。

官方 `Node` 物理顺序：left / right / parent / color / key / value。
`SENTINEL = 0`，已分配地址从 1 起。本切片容量 4：空树写根，
非空且根右孩空时 bump 到槽 1。旋转 / 染色仍关。
-/
namespace Examples.Tree

/-- 官方 `Node<RBNode<K,V>, 4>`。地址是 1-based u64。 -/
structure Node where
  left : UInt64
  right : UInt64
  parent : UInt64
  color : UInt64
  key : UInt64
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

structure State where
  root : UInt64
  size : UInt64
  nodes : Vector Node 4
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def sentinel : UInt64 := 0

def emptyNode : Node :=
  { left := 0, right := 0, parent := 0, color := 0, key := 0, value := 0 }

@[pf_entry]
def init (_seed : UInt64) : State :=
  { root := 0, size := 0, nodes := #v[emptyNode, emptyNode, emptyNode, emptyNode] }

@[pf_entry]
def getRoot (s : State) : UInt64 :=
  s.root

@[pf_entry]
def getSize (s : State) : UInt64 :=
  s.size

/-- 读节点 0 的 value（地址 1 的槽）。 -/
@[pf_entry]
def getHead (s : State) : UInt64 :=
  s.nodes[0]!.value

/-- 写节点 0 的 value。 -/
@[pf_entry]
def setHead (s : State) (v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ s with nodes := s.nodes.set 0 { s.nodes[0]! with value := v } }, v)
  else
    .error .overflow

/--
有界 bump 分配。
空树：地址 1（槽 0）写成红根。
非空且根右孩是 SENTINEL、还有空槽：把地址 2（槽 1）挂到根右边。
满树 / 右孩已占走 overflow。旋转和染色下一刀。
-/
@[pf_entry]
def bumpInsert (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if s.root = 0 then
    if s.size = 0 then
      .ok ({ s with
              root := 1
              size := 1
              nodes := s.nodes.set 0
                { left := 0, right := 0, parent := 0, color := 1, key := k, value := v } }, k)
    else
      .error .overflow
  else if s.nodes[0]!.right = 0 then
    if s.size < 4 then
      .ok ({ s with
              size := s.size + 1
              nodes :=
                (s.nodes.set 0 { s.nodes[0]! with right := 2 }).set 1
                  { left := 0, right := 0, parent := 1, color := 1, key := k, value := v } }, k)
    else
      .error .overflow
  else
    .error .overflow

end Examples.Tree
