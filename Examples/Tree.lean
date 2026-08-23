import ProofForge

/-!
Sokoban 红黑树节点 + 定长 `Vector`。

官方 `Node` 物理顺序：left / right / parent / color / key / value。
`SENTINEL = 0`，已分配地址从 1 起。本切片容量 4。allocator 对齐 Sokoban：
`bumpIndex/freeHead` 初值 1，一过尾标记 5，free node 的 `left` 复用作 LIFO next。
树插入仍只保留两节点 smoke path；完整 fixup / deletion 后续继续。
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
  bumpIndex : UInt64
  freeHead : UInt64
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
  { root := 0, size := 0, bumpIndex := 1, freeHead := 1,
    nodes := #v[emptyNode, emptyNode, emptyNode, emptyNode] }

@[pf_entry]
def getRoot (s : State) : UInt64 :=
  s.root

@[pf_entry]
def getSize (s : State) : UInt64 :=
  s.size

@[pf_entry]
def getBumpIndex (s : State) : UInt64 :=
  s.bumpIndex

@[pf_entry]
def getFreeHead (s : State) : UInt64 :=
  s.freeHead

/-- 读节点 0 的 value（地址 1 的槽）。 -/
@[pf_entry]
def getHead (s : State) : UInt64 :=
  s.nodes[0]!.value

/-- 运行时下标读节点 value。 -/
@[pf_entry]
def getAt (s : State) (i : UInt64) : UInt64 :=
  if i < 4 then s.nodes[i.toNat]!.value else 0

/-- 写节点 0 的 value。 -/
@[pf_entry]
def setHead (s : State) (v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ s with nodes := s.nodes.set 0 { s.nodes[0]! with value := v } }, v)
  else
    .error .overflow

/-- 运行时下标写节点 value。 -/
@[pf_entry]
def setAt (s : State) (i v : UInt64) : Except Error (State × UInt64) :=
  if h : i.toNat < 4 then
    .ok ({ s with nodes := s.nodes.set i.toNat { s.nodes[i.toNat]! with value := v } }, v)
  else
    .error .overflow

/-- 运行时下标读 right。 -/
@[pf_entry]
def getRight (s : State) (i : UInt64) : UInt64 :=
  if i < 4 then s.nodes[i.toNat]!.right else 0

/-- 运行时下标写 right。旋转会用。 -/
@[pf_entry]
def setRight (s : State) (i child : UInt64) : Except Error (State × UInt64) :=
  if h : i.toNat < 4 then
    .ok ({ s with nodes := s.nodes.set i.toNat { s.nodes[i.toNat]! with right := child } }, child)
  else
    .error .overflow

/-- 运行时下标写 parent。 -/
@[pf_entry]
def setParent (s : State) (i p : UInt64) : Except Error (State × UInt64) :=
  if h : i.toNat < 4 then
    .ok ({ s with nodes := s.nodes.set i.toNat { s.nodes[i.toNat]! with parent := p } }, p)
  else
    .error .overflow

/--
Sokoban `NodeAllocator.add_node` 的 N=4 版本。`freeHead = bumpIndex` 时从 bump
区分配，否则弹出 free node；复用时把作为 next-free 的 `left` 清零。返回 1-based 地址。
-/
@[pf_entry]
def allocNode (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if s.size < 4 then
    if s.freeHead = s.bumpIndex then
      if s.bumpIndex = 0 then
        .error .overflow
      else if s.bumpIndex < 5 then
        let address := s.bumpIndex
        let i := address.toNat - 1
        .ok ({ s with
                size := s.size + 1
                bumpIndex := s.bumpIndex + 1
                freeHead := s.bumpIndex + 1
                nodes := s.nodes.set (i % 4)
                  { left := 0, right := 0, parent := 0, color := 0, key := k, value := v } },
          address)
      else
        .error .overflow
    else if s.freeHead = 0 then
      .error .overflow
    else if s.freeHead < 5 then
      let address := s.freeHead
      let i := address.toNat - 1
      let next := s.nodes[i]!.left
      .ok ({ s with
              size := s.size + 1
              freeHead := next
              nodes := s.nodes.set (i % 4)
                { left := 0, right := 0, parent := 0, color := 0, key := k, value := v } },
        address)
    else
      .error .overflow
  else
    .error .overflow

/--
树层 release：先清 right/parent/color，再由 allocator 把 `left` 写成旧 freeHead。
key/value 按 Sokoban remove_node 保留，下一次 allocation 才覆盖 payload。
-/
@[pf_entry]
def releaseNode (s : State) (address : UInt64) : Except Error (State × UInt64) :=
  if address = 0 then
    .error .overflow
  else if address < s.bumpIndex then
    if h : address.toNat - 1 < 4 then
      if s.size = 0 then
        .error .overflow
      else
        let i := address.toNat - 1
        let old := s.nodes[i]!
        .ok ({ s with
                size := s.size - 1
                freeHead := address
                nodes := s.nodes.set i
                  { old with left := s.freeHead, right := 0, parent := 0, color := 0 } },
          address)
    else
      .error .overflow
  else
    .error .overflow

/--
有界 bump 分配。
空树：地址 1（槽 0）写成红根。
非空且根右孩是 SENTINEL、还有空槽：把地址 2（槽 1）挂到根右边。
满树 / 右孩已占走 overflow。旋转已开；染色仍关。
-/
@[pf_entry]
def bumpInsert (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if s.root = 0 then
    if s.size = 0 then
      .ok ({ s with
              root := 1
              size := 1
              bumpIndex := 2
              freeHead := 2
              nodes := s.nodes.set 0
                { left := 0, right := 0, parent := 0, color := 1, key := k, value := v } }, k)
    else
      .error .overflow
  else if s.nodes[0]!.right = 0 then
    if s.size < 4 then
      if s.bumpIndex = 2 then
        if s.freeHead = 2 then
      .ok ({ s with
              size := s.size + 1
              bumpIndex := 3
              freeHead := 3
              nodes :=
                (s.nodes.set 0 { s.nodes[0]! with right := 2 }).set 1
                  { left := 0, right := 0, parent := 1, color := 1, key := k, value := v } }, k)
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- 完整左旋。参数和返回值都是 1-based 地址，0 只作 sentinel。 -/
@[pf_entry]
def rotateLeft (s : State) (xAddress : UInt64) : Except Error (State × UInt64) :=
  if xAddress = 0 then
    .error .overflow
  else if hx : xAddress.toNat - 1 < 4 then
    let xi := xAddress.toNat - 1
    let x := s.nodes[xi]!
    let yAddress := x.right
    if yAddress = 0 then
      .error .overflow
    else if hy : yAddress.toNat - 1 < 4 then
      let yi := yAddress.toNat - 1
      let y := s.nodes[yi]!
      let innerAddress := y.left
      let parentAddress := x.parent
      if 4 < innerAddress then
        .error .overflow
      else if 4 < parentAddress then
        .error .overflow
      else
        let nodes1 := s.nodes.set xi { x with right := innerAddress, parent := yAddress }
        if innerAddress = 0 then
          if parentAddress = 0 then
            let rotated :=
              nodes1.set yi { nodes1[yi]! with left := xAddress, parent := 0 }
            .ok ({ s with root := yAddress, nodes := rotated }, yAddress)
          else
            let parentIndex := (parentAddress.toNat - 1) % 4
            if nodes1[parentIndex]!.left = xAddress then
              let rotated :=
                (nodes1.set parentIndex { nodes1[parentIndex]! with left := yAddress }).set yi
                  { nodes1[yi]! with left := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
            else
              let rotated :=
                (nodes1.set parentIndex { nodes1[parentIndex]! with right := yAddress }).set yi
                  { nodes1[yi]! with left := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
        else
          let innerIndex := (innerAddress.toNat - 1) % 4
          let nodes2 :=
            nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
          if parentAddress = 0 then
            let rotated :=
              nodes2.set yi { nodes2[yi]! with left := xAddress, parent := 0 }
            .ok ({ s with root := yAddress, nodes := rotated }, yAddress)
          else
            let parentIndex := (parentAddress.toNat - 1) % 4
            if nodes2[parentIndex]!.left = xAddress then
              let rotated :=
                (nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }).set yi
                  { nodes2[yi]! with left := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
            else
              let rotated :=
                (nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }).set yi
                  { nodes2[yi]! with left := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
    else
      .error .overflow
  else
    .error .overflow

/-- 完整右旋。参数和返回值都是 1-based 地址，0 只作 sentinel。 -/
@[pf_entry]
def rotateRight (s : State) (xAddress : UInt64) : Except Error (State × UInt64) :=
  if xAddress = 0 then
    .error .overflow
  else if hx : xAddress.toNat - 1 < 4 then
    let xi := xAddress.toNat - 1
    let x := s.nodes[xi]!
    let yAddress := x.left
    if yAddress = 0 then
      .error .overflow
    else if hy : yAddress.toNat - 1 < 4 then
      let yi := yAddress.toNat - 1
      let y := s.nodes[yi]!
      let innerAddress := y.right
      let parentAddress := x.parent
      if 4 < innerAddress then
        .error .overflow
      else if 4 < parentAddress then
        .error .overflow
      else
        let nodes1 := s.nodes.set xi { x with left := innerAddress, parent := yAddress }
        if innerAddress = 0 then
          if parentAddress = 0 then
            let rotated :=
              nodes1.set yi { nodes1[yi]! with right := xAddress, parent := 0 }
            .ok ({ s with root := yAddress, nodes := rotated }, yAddress)
          else
            let parentIndex := (parentAddress.toNat - 1) % 4
            if nodes1[parentIndex]!.left = xAddress then
              let rotated :=
                (nodes1.set parentIndex { nodes1[parentIndex]! with left := yAddress }).set yi
                  { nodes1[yi]! with right := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
            else
              let rotated :=
                (nodes1.set parentIndex { nodes1[parentIndex]! with right := yAddress }).set yi
                  { nodes1[yi]! with right := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
        else
          let innerIndex := (innerAddress.toNat - 1) % 4
          let nodes2 :=
            nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
          if parentAddress = 0 then
            let rotated :=
              nodes2.set yi { nodes2[yi]! with right := xAddress, parent := 0 }
            .ok ({ s with root := yAddress, nodes := rotated }, yAddress)
          else
            let parentIndex := (parentAddress.toNat - 1) % 4
            if nodes2[parentIndex]!.left = xAddress then
              let rotated :=
                (nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }).set yi
                  { nodes2[yi]! with right := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
            else
              let rotated :=
                (nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }).set yi
                  { nodes2[yi]! with right := xAddress, parent := parentAddress }
              .ok ({ s with nodes := rotated }, yAddress)
    else
      .error .overflow
  else
    .error .overflow

/-!
N=4 的合法树在新插入前最多 3 个节点，因此 insertion fixup 最多执行一轮，且发生
红父冲突时 grandparent 必为 root。下面仍完整区分 red-uncle、LL/RR 和 LR/RL；
结果与 Sokoban `_fix_insert` 在该有界可达状态空间上一致。
-/

private def fixInserted (before s : State) (nodeAddress parentAddress direction : UInt64) :
    Except Error (State × UInt64) :=
  let parentIndex := (parentAddress.toNat - 1) % 4
  if before.nodes[parentIndex]!.color = 1 then
    let grandAddress := before.nodes[parentIndex]!.parent
    if grandAddress = 0 then
      let nodes :=
        s.nodes.set parentIndex { s.nodes[parentIndex]! with color := 0 }
      .ok ({ s with nodes }, nodeAddress)
    else
      let grandIndex := (grandAddress.toNat - 1) % 4
      if before.nodes[grandIndex]!.left = parentAddress then
        let uncleAddress := before.nodes[grandIndex]!.right
        let uncleIndex := (uncleAddress.toNat - 1) % 4
        let uncleColor : UInt64 :=
          if uncleAddress = 0 then 0 else before.nodes[uncleIndex]!.color
        if uncleColor = 1 then
          let nodes :=
            ((s.nodes.set parentIndex { s.nodes[parentIndex]! with color := 0 }).set
              uncleIndex { s.nodes[uncleIndex]! with color := 0 }).set grandIndex
              { s.nodes[grandIndex]! with color := 0 }
          .ok ({ s with nodes }, nodeAddress)
        else if direction = 1 then
          let nodeIndex := (nodeAddress.toNat - 1) % 4
          let nodes :=
            (((s.nodes.set parentIndex
                { s.nodes[parentIndex]! with
                  right := 0
                  parent := nodeAddress
                  color := 1 }).set
              grandIndex
                { s.nodes[grandIndex]! with
                  left := 0
                  parent := nodeAddress
                  color := 1 }).set
              nodeIndex
                { s.nodes[nodeIndex]! with
                  left := parentAddress
                  right := grandAddress
                  parent := 0
                  color := 0 })
          .ok ({ s with root := nodeAddress, nodes := nodes }, nodeAddress)
        else
          let nodes :=
            (s.nodes.set grandIndex
                { s.nodes[grandIndex]! with
                  left := 0
                  parent := parentAddress
                  color := 1 }).set
              parentIndex
                { s.nodes[parentIndex]! with
                  right := grandAddress
                  parent := 0
                  color := 0 }
          .ok ({ s with root := parentAddress, nodes := nodes }, nodeAddress)
      else
        let uncleAddress := before.nodes[grandIndex]!.left
        let uncleIndex := (uncleAddress.toNat - 1) % 4
        let uncleColor : UInt64 :=
          if uncleAddress = 0 then 0 else before.nodes[uncleIndex]!.color
        if uncleColor = 1 then
          let nodes :=
            ((s.nodes.set parentIndex { s.nodes[parentIndex]! with color := 0 }).set
              uncleIndex { s.nodes[uncleIndex]! with color := 0 }).set grandIndex
              { s.nodes[grandIndex]! with color := 0 }
          .ok ({ s with nodes }, nodeAddress)
        else if direction = 0 then
          let nodeIndex := (nodeAddress.toNat - 1) % 4
          let nodes :=
            (((s.nodes.set parentIndex
                { s.nodes[parentIndex]! with
                  left := 0
                  parent := nodeAddress
                  color := 1 }).set
              grandIndex
                { s.nodes[grandIndex]! with
                  right := 0
                  parent := nodeAddress
                  color := 1 }).set
              nodeIndex
                { s.nodes[nodeIndex]! with
                  left := grandAddress
                  right := parentAddress
                  parent := 0
                  color := 0 })
          .ok ({ s with root := nodeAddress, nodes := nodes }, nodeAddress)
        else
          let nodes :=
            (s.nodes.set grandIndex
                { s.nodes[grandIndex]! with
                  right := 0
                  parent := parentAddress
                  color := 1 }).set
              parentIndex
                { s.nodes[parentIndex]! with
                  left := grandAddress
                  parent := 0
                  color := 0 }
          .ok ({ s with root := parentAddress, nodes := nodes }, nodeAddress)
  else
    .ok (s, nodeAddress)

attribute [pf_inline] fixInserted

private def insertAt (s : State) (parentAddress direction k v : UInt64) :
    Except Error (State × UInt64) :=
  if s.size < 4 then
    let parentIndex := (parentAddress.toNat - 1) % 4
    let fresh : UInt64 := if s.freeHead = s.bumpIndex then 1 else 0
    let valid : UInt64 :=
      if fresh = 1 then
        if s.bumpIndex = 0 then 0 else if s.bumpIndex < 5 then 1 else 0
      else
        if s.freeHead = 0 then 0 else if s.freeHead < 5 then 1 else 0
    if valid = 1 then
      let address := if fresh = 1 then s.bumpIndex else s.freeHead
      let i := (address.toNat - 1) % 4
      let freeNext := s.nodes[i]!.left
      let nextBump := if fresh = 1 then s.bumpIndex + 1 else s.bumpIndex
      let nextFree := if fresh = 1 then s.bumpIndex + 1 else freeNext
      let parent := s.nodes[parentIndex]!
      let linkedParent :=
        if direction = 0 then { parent with left := address }
        else { parent with right := address }
      let nodes :=
        (s.nodes.set parentIndex linkedParent).set i
          { left := 0
            right := 0
            parent := parentAddress
            color := 1
            key := k
            value := v }
      let linked :=
        { s with
          size := s.size + 1
          bumpIndex := nextBump
          freeHead := nextFree
          nodes := nodes }
      fixInserted s linked address parentAddress direction
    else
      .error .overflow
  else
    .error .overflow

attribute [pf_inline] insertAt

private def insertRoot (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if s.size < 4 then
    let fresh : UInt64 := if s.freeHead = s.bumpIndex then 1 else 0
    let valid : UInt64 :=
      if fresh = 1 then
        if s.bumpIndex = 0 then 0 else if s.bumpIndex < 5 then 1 else 0
      else
        if s.freeHead = 0 then 0 else if s.freeHead < 5 then 1 else 0
    if valid = 1 then
      let address := if fresh = 1 then s.bumpIndex else s.freeHead
      let i := (address.toNat - 1) % 4
      let freeNext := s.nodes[i]!.left
      let nextBump := if fresh = 1 then s.bumpIndex + 1 else s.bumpIndex
      let nextFree := if fresh = 1 then s.bumpIndex + 1 else freeNext
      .ok ({ s with
              root := address
              size := s.size + 1
              bumpIndex := nextBump
              freeHead := nextFree
              nodes := s.nodes.set i
                { left := 0
                  right := 0
                  parent := 0
                  color := 0
                  key := k
                  value := v } },
        address)
    else
      .error .overflow
  else
    .error .overflow

attribute [pf_inline] insertRoot

/-- Sokoban `insert` 的 N=4 特化：duplicate 覆盖 value，否则分配红叶并执行 fixup。 -/
@[pf_entry]
def insertNode (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if s.root = 0 then
    insertRoot s k v
  else
    -- Keep bounded search as a linear chain of conditional values. Expanding each comparison as
    -- control flow would duplicate the allocator/fixup at every leaf.
    let a0 := s.root
    let i0 := (a0.toNat - 1) % 4
    let n0 := s.nodes[i0]!
    let a1 := if k = n0.key then 0 else if k < n0.key then n0.left else n0.right
    let i1 := (a1.toNat - 1) % 4
    let n1 := s.nodes[i1]!
    let a2 :=
      if a1 = 0 then 0
      else if k = n1.key then 0
      else if k < n1.key then n1.left else n1.right
    let i2 := (a2.toNat - 1) % 4
    let n2 := s.nodes[i2]!
    let a3 :=
      if a2 = 0 then 0
      else if k = n2.key then 0
      else if k < n2.key then n2.left else n2.right
    let i3 := (a3.toNat - 1) % 4
    let n3 := s.nodes[i3]!
    let found :=
      if k = n0.key then a0
      else if a1 = 0 then 0
      else if k = n1.key then a1
      else if a2 = 0 then 0
      else if k = n2.key then a2
      else if a3 = 0 then 0
      else if k = n3.key then a3 else 0
    if found ≠ 0 then
      let foundIndex := (found.toNat - 1) % 4
      .ok ({ s with nodes := s.nodes.set foundIndex { s.nodes[foundIndex]! with value := v } },
        found)
    else
      let parent := if a3 ≠ 0 then a3 else if a2 ≠ 0 then a2 else if a1 ≠ 0 then a1 else a0
      let parentIndex := (parent.toNat - 1) % 4
      let direction : UInt64 := if k < s.nodes[parentIndex]!.key then 0 else 1
      insertAt s parent direction k v

end Examples.Tree
