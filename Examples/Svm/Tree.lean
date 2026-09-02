import ProofForge

/-!
Sokoban 红黑树节点 + 定长 `Vector`。

官方 `Node` 物理顺序：left / right / parent / color / key / value。
`SENTINEL = 0`，已分配地址从 1 起。本切片容量 4。allocator 对齐 Sokoban：
`bumpIndex/freeHead` 初值 1，一过尾标记 5，free node 的 `left` 复用作 LIFO next。
插入覆盖 N=4 的全部旋转/染色形状；删除按 successor transplant、bounded delete fixup，
最后把脱链地址归还同一 free list。
-/
namespace Examples.Svm.Tree

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

/-!
Delete support deliberately stays in the same N=4 refinement as insertion. A valid four-node
red-black tree can propagate a double-black node at most once: a second black parent below the
root would require at least five live nodes. `fixDeleted` therefore implements every standard
sibling case for that one reachable level rather than pretending that the fixed layout is dynamic.
-/

private def treeNode (s : State) (address : UInt64) : Node :=
  s.nodes[(address.toNat - 1) % 4]!

private def treeColor (s : State) (address : UInt64) : UInt64 :=
  if address = 0 then 0 else (treeNode s address).color

private def paintNode (s : State) (address color : UInt64) : State :=
  if address = 0 then s
  else
    let i := (address.toNat - 1) % 4
    { s with nodes := s.nodes.set i { s.nodes[i]! with color := color } }

private def linkLeft (s : State) (parent child : UInt64) : State :=
  let parentIndex := (parent.toNat - 1) % 4
  if child = 0 then
    { s with nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with left := child } }
  else
    let childIndex := (child.toNat - 1) % 4
    let nodes :=
      (s.nodes.set parentIndex { s.nodes[parentIndex]! with left := child }).set childIndex
        { s.nodes[childIndex]! with parent := parent }
    { s with nodes := nodes }

private def linkRight (s : State) (parent child : UInt64) : State :=
  let parentIndex := (parent.toNat - 1) % 4
  if child = 0 then
    { s with nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with right := child } }
  else
    let childIndex := (child.toNat - 1) % 4
    let nodes :=
      (s.nodes.set parentIndex { s.nodes[parentIndex]! with right := child }).set childIndex
        { s.nodes[childIndex]! with parent := parent }
    { s with nodes := nodes }

/-- Replace one linked subtree while preserving the replacement root's parent pointer. -/
private def transplantNode (s : State) (removed replacement : UInt64) : State :=
  let removedNode := treeNode s removed
  let parent := removedNode.parent
  let parentLinked :=
    if parent = 0 then
      { s with root := replacement }
    else
      let parentIndex := (parent.toNat - 1) % 4
      if s.nodes[parentIndex]!.left = removed then
        { s with nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with left := replacement } }
      else
        { s with nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with right := replacement } }
  if replacement = 0 then parentLinked
  else
    let replacementIndex := (replacement.toNat - 1) % 4
    { parentLinked with
      nodes := parentLinked.nodes.set replacementIndex
        { parentLinked.nodes[replacementIndex]! with parent := parent } }

/-- Internal total left rotation; callers have already established a non-sentinel right child. -/
private def rotateLeftDelete (s : State) (xAddress : UInt64) : State :=
  let xi := (xAddress.toNat - 1) % 4
  let x := s.nodes[xi]!
  let yAddress := x.right
  if yAddress = 0 then s
  else
    let yi := (yAddress.toNat - 1) % 4
    let y := s.nodes[yi]!
    let innerAddress := y.left
    let parentAddress := x.parent
    let nodes1 := s.nodes.set xi { x with right := innerAddress, parent := yAddress }
    let nodes2 :=
      if innerAddress = 0 then nodes1
      else
        let innerIndex := (innerAddress.toNat - 1) % 4
        nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    let nodes3 :=
      if parentAddress = 0 then nodes2
      else
        let parentIndex := (parentAddress.toNat - 1) % 4
        if nodes2[parentIndex]!.left = xAddress then
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        else
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
    let nodes4 :=
      nodes3.set yi { nodes3[yi]! with left := xAddress, parent := parentAddress }
    { s with
      root := if parentAddress = 0 then yAddress else s.root
      nodes := nodes4 }

/-- Internal total right rotation; callers have already established a non-sentinel left child. -/
private def rotateRightDelete (s : State) (xAddress : UInt64) : State :=
  let xi := (xAddress.toNat - 1) % 4
  let x := s.nodes[xi]!
  let yAddress := x.left
  if yAddress = 0 then s
  else
    let yi := (yAddress.toNat - 1) % 4
    let y := s.nodes[yi]!
    let innerAddress := y.right
    let parentAddress := x.parent
    let nodes1 := s.nodes.set xi { x with left := innerAddress, parent := yAddress }
    let nodes2 :=
      if innerAddress = 0 then nodes1
      else
        let innerIndex := (innerAddress.toNat - 1) % 4
        nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    let nodes3 :=
      if parentAddress = 0 then nodes2
      else
        let parentIndex := (parentAddress.toNat - 1) % 4
        if nodes2[parentIndex]!.left = xAddress then
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        else
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
    let nodes4 :=
      nodes3.set yi { nodes3[yi]! with right := xAddress, parent := parentAddress }
    { s with
      root := if parentAddress = 0 then yAddress else s.root
      nodes := nodes4 }

/-- N=4 standard delete fixup, with the sentinel parent carried separately. -/
private def fixDeleted (s : State) (xAddress parentAddress : UInt64) : State :=
  if xAddress = s.root then
    paintNode s xAddress 0
  else if treeColor s xAddress = 1 then
    paintNode s xAddress 0
  else if parentAddress = 0 then
    paintNode s xAddress 0
  else
    let parent := treeNode s parentAddress
    if parent.left = xAddress then
      let firstSibling := parent.right
      let afterRedSibling :=
        if treeColor s firstSibling = 1 then
          let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
          rotateLeftDelete recolored parentAddress
        else s
      let sibling := (treeNode afterRedSibling parentAddress).right
      let nearChild := (treeNode afterRedSibling sibling).left
      let farChild := (treeNode afterRedSibling sibling).right
      if treeColor afterRedSibling nearChild = 0 && treeColor afterRedSibling farChild = 0 then
        let siblingRed := paintNode afterRedSibling sibling 1
        -- If the parent is black it is necessarily the root in a valid N=4 tree.
        paintNode siblingRed parentAddress 0
      else
        let aligned :=
          if treeColor afterRedSibling farChild = 0 then
            let recolored :=
              paintNode (paintNode afterRedSibling nearChild 0) sibling 1
            rotateRightDelete recolored sibling
          else afterRedSibling
        let alignedSibling := (treeNode aligned parentAddress).right
        let alignedFar := (treeNode aligned alignedSibling).right
        let parentColor := treeColor aligned parentAddress
        let recolored :=
          paintNode
            (paintNode (paintNode aligned alignedSibling parentColor) parentAddress 0)
            alignedFar 0
        rotateLeftDelete recolored parentAddress
    else
      let firstSibling := parent.left
      let afterRedSibling :=
        if treeColor s firstSibling = 1 then
          let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
          rotateRightDelete recolored parentAddress
        else s
      let sibling := (treeNode afterRedSibling parentAddress).left
      let nearChild := (treeNode afterRedSibling sibling).right
      let farChild := (treeNode afterRedSibling sibling).left
      if treeColor afterRedSibling nearChild = 0 && treeColor afterRedSibling farChild = 0 then
        let siblingRed := paintNode afterRedSibling sibling 1
        paintNode siblingRed parentAddress 0
      else
        let aligned :=
          if treeColor afterRedSibling farChild = 0 then
            let recolored :=
              paintNode (paintNode afterRedSibling nearChild 0) sibling 1
            rotateLeftDelete recolored sibling
          else afterRedSibling
        let alignedSibling := (treeNode aligned parentAddress).left
        let alignedFar := (treeNode aligned alignedSibling).left
        let parentColor := treeColor aligned parentAddress
        let recolored :=
          paintNode
            (paintNode (paintNode aligned alignedSibling parentColor) parentAddress 0)
            alignedFar 0
        rotateRightDelete recolored parentAddress

/-- Move the in-order successor into a two-child node's linked position. -/
private def moveSuccessor (s : State) (removed successor replacement : UInt64) : State :=
  let removedNode := treeNode s removed
  let successorNode := treeNode s successor
  if successorNode.parent = removed then
    let moved := transplantNode s removed successor
    let withLeft := linkLeft moved successor removedNode.left
    paintNode withLeft successor removedNode.color
  else
    let detached := transplantNode s successor replacement
    let withRight := linkRight detached successor removedNode.right
    let moved := transplantNode withRight removed successor
    let withLeft := linkLeft moved successor removedNode.left
    paintNode withLeft successor removedNode.color

/-- Return a detached tree node to the Sokoban LIFO free list. -/
private def releaseRemoved (s : State) (address : UInt64) : State :=
  let i := (address.toNat - 1) % 4
  let old := s.nodes[i]!
  { s with
    size := s.size - 1
    freeHead := address
    nodes := s.nodes.set i
      { old with left := s.freeHead, right := 0, parent := 0, color := 0 } }

attribute [pf_inline] treeNode treeColor paintNode linkLeft linkRight transplantNode
  rotateLeftDelete rotateRightDelete fixDeleted moveSuccessor releaseRemoved

/--
Sokoban-style key removal. The node is structurally detached, black-height is repaired, then its
address is pushed onto the allocator free list. The removed address is returned for refinement
tests and deterministic reuse checks.
-/
@[pf_entry]
def removeNode (s : State) (k : UInt64) : Except Error (State × UInt64) :=
  -- Keep the bounded lookup in the entry body so every comparison remains a typed scalar value.
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
  let removedAddress :=
    if k = n0.key then a0
    else if a1 = 0 then 0
    else if k = n1.key then a1
    else if a2 = 0 then 0
    else if k = n2.key then a2
    else if a3 = 0 then 0
    else if k = n3.key then a3 else 0
  if removedAddress = 0 then
    .error .overflow
  else
    let removedIndex := (removedAddress.toNat - 1) % 4
    let removed := s.nodes[removedIndex]!
    let successorRoot := removed.right
    let successorLeft1 := s.nodes[(successorRoot.toNat - 1) % 4]!.left
    let successorLeft2 :=
      if successorLeft1 = 0 then 0
      else s.nodes[(successorLeft1.toNat - 1) % 4]!.left
    let successorAddress :=
      if removed.left = 0 || removed.right = 0 then removedAddress
      else if successorLeft2 ≠ 0 then successorLeft2
      else if successorLeft1 ≠ 0 then successorLeft1
      else successorRoot
    let successorIndex := (successorAddress.toNat - 1) % 4
    let successor := s.nodes[successorIndex]!
    let removedColor := successor.color
    let replacementAddress :=
      if successor.left ≠ 0 then successor.left else successor.right
    let replacementParent :=
      if successorAddress = removedAddress then removed.parent
      else if successor.parent = removedAddress then successorAddress
      else successor.parent
    let moved :=
      if removed.left = 0 then
        transplantNode s removedAddress removed.right
      else if removed.right = 0 then
        transplantNode s removedAddress removed.left
      else
        moveSuccessor s removedAddress successorAddress replacementAddress
    let fixed :=
      if removedColor = 0 then fixDeleted moved replacementAddress replacementParent else moved
    let rootBlack := paintNode fixed fixed.root 0
    let released := releaseRemoved rootBlack removedAddress
    .ok (released, removedAddress)

section Proofs

/-! ### 良构谓词（WF）第一批切片：分配器几何 + 指针有界

`wf` 是 insertNode / removeNode 的 BST 有序性证明要建立在上面的不变量基础。
本切片只收「分配器 + 链接指针有界」；BST 全序需要先证可达集与自由集分离，
是 p-004 的主体。 -/

/-- N=4 树的分配器与指针几何良构：
- `size ≤ 4`；bump 游标在 `[1, 5]`；freeHead 是哨兵或槽地址且不超前 bump；
- 每个 bump 区节点（地址 `[1, bumpIndex)`）的 left/right/parent 都是哨兵或槽地址，
  color 是 0/1。 -/
def wf (s : State) : Prop :=
  s.size ≤ 4 ∧ 1 ≤ s.bumpIndex ∧ s.bumpIndex ≤ 5 ∧ s.freeHead ≤ 5 ∧
    s.freeHead ≤ s.bumpIndex ∧
    (∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
      s.nodes[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
      s.nodes[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
      s.nodes[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
      s.nodes[(a.toNat - 1) % 4]!.color ≤ 1)

/-- 槽位映射 `a ↦ (a-1) % 4` 在槽地址 `[1, 5)` 上单射。 -/
private theorem vec_set_self {α : Type} [Inhabited α] {n : Nat} (xs : Vector α n)
    (i : Nat) (x : α) (hi : i < n) : (xs.set i x hi)[i]! = x := by
  show (xs.set i x hi)[i]?.get! = x
  have h2 : (xs.set i x hi)[i]? = some x := by simp
  rw [h2]
  rfl

private theorem slot_inj {a b : UInt64} (ha : 1 ≤ a) (ha4 : a < 5) (hb : 1 ≤ b) (hb4 : b < 5)
    (h : (a.toNat - 1) % 4 = (b.toNat - 1) % 4) : a = b := by
  refine UInt64.toNat_inj.mp ?_
  have h0 : (1 : Nat) ≤ a.toNat := ha
  have h1 : a.toNat < 5 := ha4
  have h2 : (1 : Nat) ≤ b.toNat := hb
  have h3 : b.toNat < 5 := hb4
  omega

private theorem vec_set2_get_right {α : Type} [Inhabited α] {n : Nat} (xs : Vector α n)
    (i j : Nat) (x y : α) (hi : i < n) (hj : j < n) :
    ((xs.set i x hi).set j y hj)[j]! = y := by
  show ((xs.set i x hi).set j y hj)[j]?.get! = y
  have h2 : ((xs.set i x hi).set j y hj)[j]? = some y := by simp [Vector.getElem_set, hj]
  rw [h2]; rfl

private theorem vec_set2_get_left {α : Type} [Inhabited α] {n : Nat} (xs : Vector α n)
    (i j : Nat) (x y : α) (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    ((xs.set i x hi).set j y hj)[i]! = x := by
  show ((xs.set i x hi).set j y hj)[i]?.get! = x
  have h2 : ((xs.set i x hi).set j y hj)[i]? = some x := by
    simp [Vector.getElem_set, Ne.symm hne, hi]
  rw [h2]; rfl

private theorem u64_toNat_add_one {a : UInt64} (h : a < 6) : (a + 1).toNat = a.toNat + 1 := by
  have hone : UInt64.toNat 1 = 1 := rfl
  have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
  rw [UInt64.toNat_add, hone, h2]
  have hnat : a.toNat < 6 := h
  have hlt : a.toNat + 1 < 4294967296 * 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt]

theorem init_wf (x : UInt64) : wf (init x) := by
  unfold wf init
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  -- bumpIndex(init) = 1，故 1 ≤ a < 1 无解
  intro a ha0 ha1
  have h0 : (1 : Nat) ≤ a.toNat := ha0
  have h1 : a.toNat < 1 := ha1
  omega

private theorem u64_succ_bound {a : UInt64} (h : a < 4) : (a + 1).toNat ≤ 4 := by
  have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
  have hnat : a.toNat < 4 := h
  have hone : UInt64.toNat 1 = 1 := rfl
  rw [UInt64.toNat_add, h2, hone]
  have hlt : a.toNat + 1 < 4294967296 * 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- **allocNode 保持 wf**：bump 分支游标 +1、free-list 分支弹出链头，
两种成功路径都不产生越界指针。 -/
theorem allocNode_wf (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : allocNode s k v = .ok (t, a)) (hwf : wf s) : wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  unfold allocNode at h
  split at h
  · rename_i hsz4
    split at h
    · -- B-T：bump 分支（freeHead = bumpIndex）
      split at h
      · simp at h
      · rename_i hc0
        split at h
        · -- D-T 成功
          rename_i hb4
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hb : s.bumpIndex.toNat < 5 := hb4
          have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
            u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
          refine ⟨?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
            omega
          · show (1 : Nat) ≤ (s.bumpIndex + 1).toNat
            have hb1' : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
            rw [hbi]
            omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]
            omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]
            omega
          · intro a ha0 ha1
            have ha1' : a.toNat < (s.bumpIndex + 1).toNat := ha1
            rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)] at ha1'
            by_cases hab : a = s.bumpIndex
            · rw [hab, vec_set_self]
              exact ⟨by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.bumpIndex.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by omega
                exact hab (slot_inj ha0 ha5 hb1 hb heq)
              have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
              have hlt : a < s.bumpIndex := by
                have hne : a.toNat ≠ s.bumpIndex.toNat := by
                  intro heq; exact hab (UInt64.toNat_inj.mp heq)
                show a.toNat < s.bumpIndex.toNat
                omega
              have hget : (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                (by omega))[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
                show (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]?.get! = _
                have h2 : (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
                  simp [Vector.getElem_set, Ne.symm hslot_ne]
                rw [h2]
                simp [hslot_lt]
              simp only []
              rw [hget]
              obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 hlt
              refine ⟨?_, ?_, ?_, ?_⟩
              · show (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat := hr
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat := hp
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · exact hc
        · simp at h
    · -- B-F：free-list 分支
      rename_i hfbne
      split at h
      · simp at h
      · rename_i he0
        split at h
        · -- F2-T 成功
          rename_i hf4
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne0 : s.freeHead.toNat ≠ 0 := by
            intro heq; exact he0 (UInt64.toNat_inj.mp heq)
          have hb1' : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
          have hle' : s.freeHead.toNat ≤ s.bumpIndex.toNat := hfb
          have hb5' : s.bumpIndex.toNat ≤ 5 := hb5
          have hfh : (1 : Nat) ≤ s.freeHead.toNat := by omega
          have hfblt : s.freeHead.toNat < s.bumpIndex.toNat := by
            have hne : s.freeHead.toNat ≠ s.bumpIndex.toNat := fun heq =>
              hfbne (UInt64.toNat_inj.mp heq)
            omega
          have hfh4 : s.freeHead < 5 := by
            show s.freeHead.toNat < 5
            omega
          have hmod : (s.freeHead.toNat - 1) % 4 = s.freeHead.toNat - 1 := by
            have h2 : s.freeHead.toNat - 1 < 4 := by omega
            exact Nat.mod_eq_of_lt h2
          have hptr' := hptr s.freeHead hfh hfblt
          obtain ⟨hl, _, _, _⟩ := hptr'
          have hl' : (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
          rw [hmod] at hl'
          have hb5' : s.bumpIndex.toNat ≤ 5 := hb5
          refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
            omega
          · show (s.nodes[s.freeHead.toNat - 1]!).left.toNat ≤ 5
            have hb : s.bumpIndex.toNat ≤ 5 := hb5
            omega
          · show (s.nodes[s.freeHead.toNat - 1]!).left ≤ s.bumpIndex
            exact hl'
          · intro a ha0 ha1
            have ha1' : a.toNat < s.bumpIndex.toNat := ha1
            by_cases hab : a = s.freeHead
            · rw [hab, vec_set_self]
              exact ⟨by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.freeHead.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by
                  have hb : s.bumpIndex.toNat ≤ 5 := hb5
                  omega
                exact hab (slot_inj ha0 ha5 hfh hfh4 heq)
              have hlt : a < s.bumpIndex := by
                have hne : a.toNat ≠ s.freeHead.toNat := by
                  intro heq; exact hab (UInt64.toNat_inj.mp heq)
                show a.toNat < s.bumpIndex.toNat
                omega
              have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
              have hget : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                (by omega))[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
                show (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]?.get! = _
                have h2 : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
                  simp [Vector.getElem_set, Ne.symm hslot_ne]
                rw [h2]
                simp [hslot_lt]
              simp only []
              rw [hget]
              obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 hlt
              refine ⟨?_, ?_, ?_, ?_⟩
              · show (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat := hr
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat := hp
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).color.toNat ≤ 1
                exact hc
        · simp at h
  · simp at h

/-- **insertRoot 保持 wf**：空树首插与 `allocNode_wf` 同构的分配路径，
额外设置 `root := address` 不改变几何 `wf` 所约束的字段。 -/
theorem insertRoot_wf (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : insertRoot s k v = .ok (t, a)) (hwf : wf s) : wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  unfold insertRoot at h
  split at h
  · rename_i hsz4
    by_cases hfbeq : s.freeHead = s.bumpIndex
    · -- bump 分支（fresh = 1）
      simp only [hfbeq, ↓reduceIte] at h
      by_cases hb0 : s.bumpIndex = 0
      · simp [hb0] at h
      · by_cases hb4 : s.bumpIndex < 5
        · -- 成功
          simp only [hb0, hb4, ↓reduceIte] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hb : s.bumpIndex.toNat < 5 := hb4
          have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
            u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
          refine ⟨?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
            omega
          · show (1 : Nat) ≤ (s.bumpIndex + 1).toNat
            have hb1' : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
            rw [hbi]
            omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]
            omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]
            omega
          · intro a ha0 ha1
            have ha1' : a.toNat < (s.bumpIndex + 1).toNat := ha1
            rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)] at ha1'
            by_cases hab : a = s.bumpIndex
            · rw [hab, vec_set_self]
              exact ⟨by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.bumpIndex.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by omega
                exact hab (slot_inj ha0 ha5 hb1 hb heq)
              have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
              have hlt : a < s.bumpIndex := by
                have hne : a.toNat ≠ s.bumpIndex.toNat := by
                  intro heq; exact hab (UInt64.toNat_inj.mp heq)
                show a.toNat < s.bumpIndex.toNat
                omega
              have hget : (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                (by omega))[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
                show (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]?.get! = _
                have h2 : (s.nodes.set ((s.bumpIndex.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
                  simp [Vector.getElem_set, Ne.symm hslot_ne]
                rw [h2]
                simp [hslot_lt]
              simp only []
              rw [hget]
              obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 hlt
              refine ⟨?_, ?_, ?_, ?_⟩
              · show (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat := hr
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ (s.bumpIndex + 1).toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat := hp
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]
                omega
              · exact hc
        · simp [hb4] at h
    · -- free-list 分支（fresh = 0）
      simp only [hfbeq, ↓reduceIte] at h
      by_cases he0 : s.freeHead = 0
      · simp [he0] at h
      · by_cases hf4 : s.freeHead < 5
        · -- 成功
          simp only [he0, hf4, ↓reduceIte] at h
          dsimp at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne0 : s.freeHead.toNat ≠ 0 := by
            intro heq; exact he0 (UInt64.toNat_inj.mp heq)
          have hb1' : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
          have hle' : s.freeHead.toNat ≤ s.bumpIndex.toNat := hfb
          have hb5' : s.bumpIndex.toNat ≤ 5 := hb5
          have hfh : (1 : Nat) ≤ s.freeHead.toNat := by omega
          have hfblt : s.freeHead.toNat < s.bumpIndex.toNat := by
            have hne : s.freeHead.toNat ≠ s.bumpIndex.toNat := fun heq =>
              hfbeq (UInt64.toNat_inj.mp heq)
            omega
          have hfh4 : s.freeHead < 5 := by
            show s.freeHead.toNat < 5
            omega
          have hmod : (s.freeHead.toNat - 1) % 4 = s.freeHead.toNat - 1 := by
            have h2 : s.freeHead.toNat - 1 < 4 := by omega
            exact Nat.mod_eq_of_lt h2
          have hptr' := hptr s.freeHead hfh hfblt
          obtain ⟨hl, _, _, _⟩ := hptr'
          have hl' : (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
          rw [hmod] at hl'
          refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
            omega
          · show (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ 5
            have hl5 : (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
            omega
          · show (s.nodes[(s.freeHead.toNat - 1) % 4]!).left ≤ s.bumpIndex
            exact hl
          · intro a ha0 ha1
            have ha1' : a.toNat < s.bumpIndex.toNat := ha1
            by_cases hab : a = s.freeHead
            · rw [hab, vec_set_self]
              exact ⟨by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _, by exact Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.freeHead.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by
                  have hb : s.bumpIndex.toNat ≤ 5 := hb5
                  omega
                exact hab (slot_inj ha0 ha5 hfh hfh4 heq)
              have hlt : a < s.bumpIndex := by
                have hne : a.toNat ≠ s.freeHead.toNat := by
                  intro heq; exact hab (UInt64.toNat_inj.mp heq)
                show a.toNat < s.bumpIndex.toNat
                omega
              have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
              have hget : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                (by omega))[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
                show (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]?.get! = _
                have h2 : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  (by omega))[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
                  simp [Vector.getElem_set, Ne.symm hslot_ne]
                rw [h2]
                simp [hslot_lt]
              simp only []
              rw [hget]
              obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 hlt
              refine ⟨?_, ?_, ?_, ?_⟩
              · show (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat := hr
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat
                have hf' : (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat := hp
                omega
              · show (s.nodes[(a.toNat - 1) % 4]!).color.toNat ≤ 1
                exact hc
        · simp [hf4] at h
  · simp at h

/-- **insertNode 空树路径保持 wf**：`root = 0` 时分派到 `insertRoot`。 -/
theorem insertNode_wf_root (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : insertNode s k v = .ok (t, a)) (hwf : wf s) (hroot : s.root = 0) : wf t := by
  unfold insertNode at h
  simp only [hroot, ↓reduceIte] at h
  exact insertRoot_wf s k v h hwf

/-! ## 第二批 kernel 证明：N=4 分配器与旋转的结构不变量

`u64_pred_add`：`(a-1)+1 = a` 对 UInt64 无条件成立（模 2^64），所以 removeNode
的 size 结论不需要「树非空」前置。 -/

private theorem u64_pred_add (a : UInt64) : (a - 1) + 1 = a := by
  refine UInt64.toNat_inj.mp ?_
  have hone : UInt64.toNat 1 = 1 := rfl
  have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
  have hsz : a.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size a
  rw [UInt64.toNat_add, UInt64.toNat_sub a 1, hone, h2, Nat.mod_add_mod]
  omega

private theorem paintNode_size (s : State) (addr c : UInt64) :
    (paintNode s addr c).size = s.size := by
  unfold paintNode
  split <;> rfl

private theorem linkLeft_size (s : State) (p c : UInt64) :
    (linkLeft s p c).size = s.size := by
  unfold linkLeft
  simp only []
  split <;> simp

private theorem linkRight_size (s : State) (p c : UInt64) :
    (linkRight s p c).size = s.size := by
  unfold linkRight
  simp only []
  split <;> simp

private theorem transplantNode_size (s : State) (r r' : UInt64) :
    (transplantNode s r r').size = s.size := by
  unfold transplantNode
  repeat (first | split | simp only [] | rfl)

private theorem rotateLeftDelete_size (s : State) (x : UInt64) :
    (rotateLeftDelete s x).size = s.size := by
  unfold rotateLeftDelete
  repeat (first | split | simp only [] | rfl)

private theorem rotateRightDelete_size (s : State) (x : UInt64) :
    (rotateRightDelete s x).size = s.size := by
  unfold rotateRightDelete
  repeat (first | split | simp only [] | rfl)

private theorem moveSuccessor_size (s : State) (rm sc rp : UInt64) :
    (moveSuccessor s rm sc rp).size = s.size := by
  unfold moveSuccessor
  repeat (first
    | split
    | simp only []
    | simp only [transplantNode_size, linkLeft_size, linkRight_size, paintNode_size]
    | rfl)

/-- `- 1 + 1` 穿过 `ite`：让 `u64_pred_add` 只在叶子处应用。 -/
private theorem sub_add_ite (c : Prop) [inst : Decidable c] (x y : UInt64) :
    (if c then x else y) - 1 + 1 = if c then (x - 1 + 1) else (y - 1 + 1) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

private theorem releaseRemoved_size (s : State) (addr : UInt64) :
    (releaseRemoved s addr).size = s.size - 1 := rfl

/-- `.size` 穿过 `ite` 的同态；removeNode 管线里的值分支靠它下推。 -/
private theorem size_ite (c : Prop) [inst : Decidable c] (x y : State) :
    (if c then x else y).size = if c then x.size else y.size := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

private theorem fixDeleted_size (s : State) (x p : UInt64) :
    (fixDeleted s x p).size = s.size := by
  unfold fixDeleted
  repeat (first
    | split
    | simp only []
    | simp only [paintNode_size, rotateLeftDelete_size, rotateRightDelete_size]
    | rfl)

/-! ## 第二批 kernel 证明：N=4 分配器与旋转的结构不变量

对上面 `@[pf_entry]` 函数的普通 kernel-checked 性质。旋转不分配/不释放节点，
分配器成功路径恰好占用一个槽；这些都是 Sokoban 组合正确性的核心前提。 -/

theorem init_state (x : UInt64) :
    getRoot (init x) = 0 ∧ getSize (init x) = 0 ∧ getBumpIndex (init x) = 1 := by
  simp [getRoot, getSize, getBumpIndex, init]

theorem setHead_roundtrip (s : State) (v : UInt64) {t : State} {r : UInt64}
    (h : setHead s v = .ok (t, r)) : getHead t = v := by
  unfold setHead at h
  unfold getHead at *
  split at h
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · simp at h

theorem setAt_roundtrip (s : State) (i v : UInt64) {t : State} {r : UInt64}
    (h : setAt s i v = .ok (t, r)) : getAt t i = v := by
  unfold setAt at h
  split at h
  · rename_i hbound
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt : i < 4 := hbound
    unfold getAt
    rw [if_pos hlt, vec_set_self]
  · simp at h

theorem allocNode_size (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : allocNode s k v = .ok (t, a)) : t.size = s.size + 1 ∧ t.size ≤ 4 := by
  unfold allocNode at h
  split at h
  · rename_i hsz
    repeat (first
      | split at h
      | simp only [] at h
      | simp at h
      | (obtain ⟨rfl, rfl⟩ := h
         refine ⟨rfl, ?_⟩
         show (s.size + 1).toNat ≤ 4
         exact u64_succ_bound hsz)
      | rfl)
  · simp at h

/-- 控制分支反演：`(if c then error E else ok R) = ok (t, a)` 给出 `¬c ∧ R = (t, a)`。
用一阶合一应用，绕开 `split` 在巨型项上的 motive elaboration。 -/
private theorem ite_except_ok_inv {c : Prop} [inst : Decidable c]
    {A B : Except Error (State × UInt64)} {t : State} {a : UInt64}
    (h : (if c then A else B) = Except.ok (t, a)) :
    B = Except.ok (t, a) ∨ A = Except.ok (t, a) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inr h
  · rw [if_neg hc] at h
    exact Or.inl h

set_option pp.deepTerms false in
/-- **removeNode 的 size 守恒**：成功删除后 `t.size + 1 = s.size`。
管线里只有 `releaseRemoved` 碰 size（`s.size - 1`），其余全部只改 nodes/root；
`(a-1)+1 = a` 对 UInt64 无条件成立，所以结论不需要非空前置。 -/
theorem removeNode_size (s : State) (k : UInt64) {t : State} {a : UInt64}
    (h : removeNode s k = .ok (t, a)) : t.size + 1 = s.size := by
  unfold removeNode at h
  simp (config := { maxSteps := 200000 }) only [] at h
  rcases ite_except_ok_inv h with hR | hE
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    -- 先把 `.size` 一路推进 ite 分支到叶子，再让 `(a-1)+1 = a` 收尾
    simp (config := { maxSteps := 200000 }) only [releaseRemoved_size, paintNode_size,
      size_ite, fixDeleted_size, transplantNode_size, moveSuccessor_size]
    simp only [u64_pred_add, ite_self]
  · simp at hE

theorem rotateLeft_size (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateLeft s x = .ok (t, y)) : t.size = s.size := by
  unfold rotateLeft at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; rfl)
    | rfl)

theorem rotateRight_size (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateRight s x = .ok (t, y)) : t.size = s.size := by
  unfold rotateRight at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; rfl)
    | rfl)

theorem rotateLeft_root (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateLeft s x = .ok (t, y)) : t.root = s.root ∨ t.root = y := by
  unfold rotateLeft at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; first
         | exact Or.inl rfl
         | exact Or.inr rfl)
    | rfl)

theorem rotateRight_root (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateRight s x = .ok (t, y)) : t.root = s.root ∨ t.root = y := by
  unfold rotateRight at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; first
         | exact Or.inl rfl
         | exact Or.inr rfl)
    | rfl)

/-! ### sf-011 第二批：局部结构算子保持几何 `wf`

旋转/链接只改 `nodes`（与 `root`），不改 `size`/`bumpIndex`/`freeHead`。
BST 有序性仍是后续切片；此处先把 p-004 的几何不变量闭包补全。 -/

private theorem u64_le_of_lt {a b : UInt64} (h : a < b) : a ≤ b :=
  (UInt64.le_iff_toNat_le).2 (Nat.le_of_lt ((UInt64.lt_iff_toNat_lt).1 h))

private theorem u64_le_trans {a b c : UInt64} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  (UInt64.le_iff_toNat_le).2
    (Nat.le_trans ((UInt64.le_iff_toNat_le).1 hab) ((UInt64.le_iff_toNat_le).1 hbc))

/-- 单槽 `nodes.set` 保持几何 `wf`，新节点指针不超过原 `bumpIndex`。 -/
private theorem wf_nodes_set (s : State) (idx : Nat) (n : Node) (hi : idx < 4) (hwf : wf s)
    (hl : n.left ≤ s.bumpIndex) (hr : n.right ≤ s.bumpIndex) (hp : n.parent ≤ s.bumpIndex)
    (hc : n.color ≤ 1) :
    wf { s with nodes := s.nodes.set idx n hi } := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  refine ⟨hsz, hb1, hb5, hf5, hfb, ?_⟩
  intro a ha0 ha1
  have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
  by_cases heq : (a.toNat - 1) % 4 = idx
  · have hidx : (s.nodes.set idx n hi)[(a.toNat - 1) % 4]! = n := by
      show (s.nodes.set idx n hi)[(a.toNat - 1) % 4]?.get! = n
      have h2 : (s.nodes.set idx n hi)[(a.toNat - 1) % 4]? = some n := by
        simp [Vector.getElem_set, heq, hslot_lt]
      rw [h2]
      rfl
    rw [hidx]
    exact ⟨hl, hr, hp, hc⟩
  · have hsame : (s.nodes.set idx n hi)[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
      show (s.nodes.set idx n hi)[(a.toNat - 1) % 4]?.get! = _
      have h2 : (s.nodes.set idx n hi)[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
        simp [Vector.getElem_set, if_neg (ne_comm.mp heq), hslot_lt]
      rw [h2]
      simp [hslot_lt]
    rw [hsame]
    exact hptr a ha0 (by simpa using ha1)

/-- **duplicate-key 路径保持 wf**：`insertNode` 命中已有 key 时只改 `value`，几何指针不变。 -/
private theorem insertNode_value_update_wf (s : State) (found v : UInt64) (hwf : wf s)
    (hf0 : 1 ≤ found) (hf1 : found < s.bumpIndex) :
    wf ({ s with
      nodes := s.nodes.set ((found.toNat - 1) % 4)
        { s.nodes[(found.toNat - 1) % 4]! with value := v }
        (by omega) }) := by
  have hi : (found.toNat - 1) % 4 < 4 := by omega
  have hnode := hwf.2.2.2.2.2 found hf0 hf1
  apply wf_nodes_set s ((found.toNat - 1) % 4)
    { s.nodes[(found.toNat - 1) % 4]! with value := v } hi hwf
  · exact hnode.1
  · exact hnode.2.1
  · exact hnode.2.2.1
  · exact hnode.2.2.2

/-- 染色只改 `color` 字段，几何指针不变（要求 `address` 落在当前 bump 区）。 -/
theorem paintNode_wf (s : State) (address color : UInt64) (hwf : wf s)
    (haddr : 1 ≤ address ∧ address < s.bumpIndex) (hc : color ≤ 1) :
    wf (paintNode s address color) := by
  unfold paintNode
  rcases haddr with ⟨ha0, ha1⟩
  have hne : address ≠ 0 := by
    intro heq
    subst heq
    have hfalse : ¬ (1 : UInt64) ≤ 0 := by decide
    exact hfalse ha0
  simp only [hne, ↓reduceIte]
  have hi : (address.toNat - 1) % 4 < 4 := by omega
  have hptr := hwf.2.2.2.2.2
  have hnode := hptr address ha0 ha1
  apply wf_nodes_set s ((address.toNat - 1) % 4)
    { s.nodes[(address.toNat - 1) % 4]! with color := color } hi hwf
  · exact hnode.1
  · exact hnode.2.1
  · exact hnode.2.2.1
  · exact hc

private theorem wf_nodes_set2 (s : State) (idx₁ idx₂ : Nat) (n₁ n₂ : Node) (hi₁ : idx₁ < 4)
    (hi₂ : idx₂ < 4) (hwf : wf s)
    (h₁ : n₁.left ≤ s.bumpIndex ∧ n₁.right ≤ s.bumpIndex ∧ n₁.parent ≤ s.bumpIndex ∧ n₁.color ≤ 1)
    (h₂ : n₂.left ≤ s.bumpIndex ∧ n₂.right ≤ s.bumpIndex ∧ n₂.parent ≤ s.bumpIndex ∧ n₂.color ≤ 1) :
    wf { s with nodes := (s.nodes.set idx₁ n₁ hi₁).set idx₂ n₂ hi₂ } := by
  rcases h₁ with ⟨hl₁, hr₁, hp₁, hc₁⟩
  rcases h₂ with ⟨hl₂, hr₂, hp₂, hc₂⟩
  exact wf_nodes_set ({ s with nodes := s.nodes.set idx₁ n₁ hi₁ }) idx₂ n₂ hi₂
    (wf_nodes_set s idx₁ n₁ hi₁ hwf hl₁ hr₁ hp₁ hc₁) hl₂ hr₂ hp₂ hc₂

/-- 三槽 `nodes.set` 保持几何 `wf`：把 `wf_nodes_set2` 的两槽结果再过一遍
`wf_nodes_set`。旋转最多同时改 `x`/`y`/`inner-或-parent` 三个槛，需要这一层组合。 -/
private theorem wf_nodes_set3 (s : State) (idx₁ idx₂ idx₃ : Nat) (n₁ n₂ n₃ : Node)
    (hi₁ : idx₁ < 4) (hi₂ : idx₂ < 4) (hi₃ : idx₃ < 4) (hwf : wf s)
    (h₁ : n₁.left ≤ s.bumpIndex ∧ n₁.right ≤ s.bumpIndex ∧ n₁.parent ≤ s.bumpIndex ∧ n₁.color ≤ 1)
    (h₂ : n₂.left ≤ s.bumpIndex ∧ n₂.right ≤ s.bumpIndex ∧ n₂.parent ≤ s.bumpIndex ∧ n₂.color ≤ 1)
    (h₃ : n₃.left ≤ s.bumpIndex ∧ n₃.right ≤ s.bumpIndex ∧ n₃.parent ≤ s.bumpIndex ∧ n₃.color ≤ 1) :
    wf { s with nodes := ((s.nodes.set idx₁ n₁ hi₁).set idx₂ n₂ hi₂).set idx₃ n₃ hi₃ } := by
  rcases h₃ with ⟨hl₃, hr₃, hp₃, hc₃⟩
  exact wf_nodes_set ({ s with nodes := (s.nodes.set idx₁ n₁ hi₁).set idx₂ n₂ hi₂ }) idx₃ n₃ hi₃
    (wf_nodes_set2 s idx₁ idx₂ n₁ n₂ hi₁ hi₂ hwf h₁ h₂) hl₃ hr₃ hp₃ hc₃

/-- 四槽 `nodes.set` 保持几何 `wf`：同上再叠一层。左旋 `innerAddress ≠ 0` 且
`parentAddress ≠ 0` 的分支要同时改 `x`/`inner`/`parent`/`y` 四个槛。 -/
private theorem wf_nodes_set4 (s : State) (idx₁ idx₂ idx₃ idx₄ : Nat) (n₁ n₂ n₃ n₄ : Node)
    (hi₁ : idx₁ < 4) (hi₂ : idx₂ < 4) (hi₃ : idx₃ < 4) (hi₄ : idx₄ < 4) (hwf : wf s)
    (h₁ : n₁.left ≤ s.bumpIndex ∧ n₁.right ≤ s.bumpIndex ∧ n₁.parent ≤ s.bumpIndex ∧ n₁.color ≤ 1)
    (h₂ : n₂.left ≤ s.bumpIndex ∧ n₂.right ≤ s.bumpIndex ∧ n₂.parent ≤ s.bumpIndex ∧ n₂.color ≤ 1)
    (h₃ : n₃.left ≤ s.bumpIndex ∧ n₃.right ≤ s.bumpIndex ∧ n₃.parent ≤ s.bumpIndex ∧ n₃.color ≤ 1)
    (h₄ : n₄.left ≤ s.bumpIndex ∧ n₄.right ≤ s.bumpIndex ∧ n₄.parent ≤ s.bumpIndex ∧ n₄.color ≤ 1) :
    wf { s with nodes :=
      (((s.nodes.set idx₁ n₁ hi₁).set idx₂ n₂ hi₂).set idx₃ n₃ hi₃).set idx₄ n₄ hi₄ } := by
  rcases h₄ with ⟨hl₄, hr₄, hp₄, hc₄⟩
  exact wf_nodes_set
    ({ s with nodes := ((s.nodes.set idx₁ n₁ hi₁).set idx₂ n₂ hi₂).set idx₃ n₃ hi₃ }) idx₄ n₄ hi₄
    (wf_nodes_set3 s idx₁ idx₂ idx₃ n₁ n₂ n₃ hi₁ hi₂ hi₃ hwf h₁ h₂ h₃) hl₄ hr₄ hp₄ hc₄

/-- 单槛读值在任意一次 `Vector.set` 之后的界：命中槛用给定的新节点界，
未命中槛沿用旧界。旋转要串接多次 `set` 时，靠它逐步推进「该槛值 ≤ bumpIndex」，
不用关心命中槛是否和之前某次 `set` 的下标重合。 -/
private theorem node_bound_set (s : State) (idx : Nat) (n : Node) (hi : idx < 4) {B : UInt64}
    (hn : n.left ≤ B ∧ n.right ≤ B ∧ n.parent ≤ B ∧ n.color ≤ 1)
    (j : Nat) (hj : j < 4)
    (ho : s.nodes[j]!.left ≤ B ∧ s.nodes[j]!.right ≤ B ∧ s.nodes[j]!.parent ≤ B ∧
      s.nodes[j]!.color ≤ 1) :
    (s.nodes.set idx n hi)[j]!.left ≤ B ∧ (s.nodes.set idx n hi)[j]!.right ≤ B ∧
      (s.nodes.set idx n hi)[j]!.parent ≤ B ∧ (s.nodes.set idx n hi)[j]!.color ≤ 1 := by
  by_cases heq : j = idx
  · rw [heq, vec_set_self s.nodes idx n hi]
    exact hn
  · have hsame : (s.nodes.set idx n hi)[j]! = s.nodes[j]! := by
      show (s.nodes.set idx n hi)[j]?.get! = _
      have h2 : (s.nodes.set idx n hi)[j]? = s.nodes[j]? := by
        simp [Vector.getElem_set, if_neg (ne_comm.mp heq), hj]
      rw [h2]
      simp [hj]
    rw [hsame]
    exact ho

/-- `linkLeft` 保持几何 `wf`（`child = 0` 时只清左子边）。 -/
theorem linkLeft_wf (s : State) (parent child : UInt64) (hwf : wf s)
    (hparent : 1 ≤ parent ∧ parent < s.bumpIndex)
    (hchild : child = 0 ∨ (1 ≤ child ∧ child < s.bumpIndex)) :
    wf (linkLeft s parent child) := by
  unfold linkLeft
  rcases hparent with ⟨hp0, hp1⟩
  have hpn := hwf.2.2.2.2.2 parent hp0 hp1
  rcases hchild with rfl | ⟨hc0, hc1⟩
  · simp only [↓reduceIte]
    apply wf_nodes_set s ((parent.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with left := 0 } (by omega) hwf
    · exact by exact Nat.zero_le _
    · exact hpn.2.1
    · exact hpn.2.2.1
    · exact hpn.2.2.2
  · have hneq : child ≠ 0 := by
      intro heq
      subst heq
      have hfalse : ¬ (1 : UInt64) ≤ 0 := by decide
      exact hfalse hc0
    simp only [if_neg hneq, ↓reduceIte]
    apply wf_nodes_set2 s ((parent.toNat - 1) % 4) ((child.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with left := child }
      { s.nodes[(child.toNat - 1) % 4]! with parent := parent } (by omega) (by omega) hwf
    · exact ⟨u64_le_of_lt hc1, hpn.2.1, hpn.2.2.1, hpn.2.2.2⟩
    · have hcn := hwf.2.2.2.2.2 child hc0 hc1
      exact ⟨hcn.1, hcn.2.1, u64_le_of_lt hp1, hcn.2.2.2⟩

/-- `linkRight` 保持几何 `wf`（`child = 0` 时只清右子边）。 -/
theorem linkRight_wf (s : State) (parent child : UInt64) (hwf : wf s)
    (hparent : 1 ≤ parent ∧ parent < s.bumpIndex)
    (hchild : child = 0 ∨ (1 ≤ child ∧ child < s.bumpIndex)) :
    wf (linkRight s parent child) := by
  unfold linkRight
  rcases hparent with ⟨hp0, hp1⟩
  have hpn := hwf.2.2.2.2.2 parent hp0 hp1
  rcases hchild with rfl | ⟨hc0, hc1⟩
  · simp only [↓reduceIte]
    apply wf_nodes_set s ((parent.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with right := 0 } (by omega) hwf
    · exact hpn.1
    · exact by exact Nat.zero_le _
    · exact hpn.2.2.1
    · exact hpn.2.2.2
  · have hneq : child ≠ 0 := by
      intro heq
      subst heq
      have hfalse : ¬ (1 : UInt64) ≤ 0 := by decide
      exact hfalse hc0
    simp only [if_neg hneq, ↓reduceIte]
    apply wf_nodes_set2 s ((parent.toNat - 1) % 4) ((child.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with right := child }
      { s.nodes[(child.toNat - 1) % 4]! with parent := parent } (by omega) (by omega) hwf
    · exact ⟨hpn.1, u64_le_of_lt hc1, hpn.2.2.1, hpn.2.2.2⟩
    · have hcn := hwf.2.2.2.2.2 child hc0 hc1
      exact ⟨hcn.1, hcn.2.1, u64_le_of_lt hp1, hcn.2.2.2⟩

private def insertAtLinkedBump (s : State) (parentAddress direction k v : UInt64) : State :=
  let address := s.bumpIndex
  let parentIndex := (parentAddress.toNat - 1) % 4
  let i := (address.toNat - 1) % 4
  let parent := s.nodes[parentIndex]!
  let linkedParent :=
    if direction = 0 then { parent with left := address }
    else { parent with right := address }
  let nodes :=
    (s.nodes.set parentIndex linkedParent).set i
      { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
  { s with size := s.size + 1, bumpIndex := s.bumpIndex + 1, freeHead := s.bumpIndex + 1, nodes := nodes }

private def insertAtLinkedFree (s : State) (parentAddress direction k v : UInt64) : State :=
  let address := s.freeHead
  let parentIndex := (parentAddress.toNat - 1) % 4
  let i := (address.toNat - 1) % 4
  let freeNext := s.nodes[i]!.left
  let parent := s.nodes[parentIndex]!
  let linkedParent :=
    if direction = 0 then { parent with left := address }
    else { parent with right := address }
  let nodes :=
    (s.nodes.set parentIndex linkedParent).set i
      { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
  { s with size := s.size + 1, freeHead := freeNext, nodes := nodes }

private theorem insertAt_linked_nodes_wf (s : State) (parentAddress direction address k v : UInt64)
    (hwf : wf s) (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (haddr : address ≤ s.bumpIndex) :
    wf { s with
      nodes := let parentIndex := (parentAddress.toNat - 1) % 4
        let i := (address.toNat - 1) % 4
        let parent := s.nodes[parentIndex]!
        let linkedParent :=
          if direction = 0 then { parent with left := address }
          else { parent with right := address }
        (s.nodes.set parentIndex linkedParent).set i
          { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
          (by omega) } := by
  obtain ⟨hp0, hp1⟩ := hparent
  have hpn := hwf.2.2.2.2.2 parentAddress hp0 hp1
  by_cases hdir : direction = 0
  · simp only [hdir, ↓reduceIte]
    apply wf_nodes_set2 s ((parentAddress.toNat - 1) % 4) ((address.toNat - 1) % 4)
      ({ s.nodes[(parentAddress.toNat - 1) % 4]! with left := address } : Node)
      { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
      (by omega) (by omega) hwf
    · exact ⟨haddr, hpn.2.1, hpn.2.2.1, hpn.2.2.2⟩
    · exact ⟨Nat.zero_le _, Nat.zero_le _, u64_le_of_lt hp1, (by decide : (1 : UInt64) ≤ 1)⟩
  · have hdir0 : direction ≠ 0 := hdir
    simp only [if_neg hdir0, ↓reduceIte]
    apply wf_nodes_set2 s ((parentAddress.toNat - 1) % 4) ((address.toNat - 1) % 4)
      ({ s.nodes[(parentAddress.toNat - 1) % 4]! with right := address } : Node)
      { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
      (by omega) (by omega) hwf
    · exact ⟨hpn.1, haddr, hpn.2.2.1, hpn.2.2.2⟩
    · exact ⟨Nat.zero_le _, Nat.zero_le _, u64_le_of_lt hp1, (by decide : (1 : UInt64) ≤ 1)⟩

theorem insertAt_linked_wf_bump (s : State) (parentAddress direction k v : UInt64)
    (hwf : wf s) (hsize : s.size.toNat < 4)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hb0 : s.bumpIndex ≠ 0) (hb4 : s.bumpIndex < 5) (hfresh : s.freeHead = s.bumpIndex) :
    wf (insertAtLinkedBump s parentAddress direction k v) := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have hwf' : wf s := ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩
  have haddr : s.bumpIndex ≤ s.bumpIndex := (UInt64.le_iff_toNat_le).2 (Nat.le_refl _)
  have hwf_nodes := insertAt_linked_nodes_wf s parentAddress direction s.bumpIndex k v hwf' hparent haddr
  have hb : s.bumpIndex.toNat < 5 := (UInt64.lt_iff_toNat_lt).mp hb4
  have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
    u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
  unfold insertAtLinkedBump
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
  · show (s.size + 1).toNat ≤ 4
    rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]; omega
  · show (1 : Nat) ≤ (s.bumpIndex + 1).toNat
    rw [hbi]; omega
  · show (s.bumpIndex + 1).toNat ≤ 5
    rw [hbi]; omega
  · show (s.bumpIndex + 1).toNat ≤ 5
    rw [hbi]; omega
  · intro a ha0 ha1
    have ha1' : a.toNat < (s.bumpIndex + 1).toNat := ha1
    rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)] at ha1'
    by_cases hab : a = s.bumpIndex
    · rw [hab]
      have hget := vec_set2_get_right s.nodes ((parentAddress.toNat - 1) % 4)
        ((s.bumpIndex.toNat - 1) % 4)
        (if direction = 0 then { s.nodes[(parentAddress.toNat - 1) % 4]! with left := s.bumpIndex }
          else { s.nodes[(parentAddress.toNat - 1) % 4]! with right := s.bumpIndex })
        { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
        (by omega) (by omega)
      rw [hget]
      have hbump_succ : s.bumpIndex < s.bumpIndex + 1 := by
        rw [UInt64.lt_iff_toNat_lt]; omega
      exact ⟨Nat.zero_le _, Nat.zero_le _, u64_le_trans (u64_le_of_lt hparent.2) (u64_le_of_lt hbump_succ),
        (by decide : (1 : UInt64) ≤ 1)⟩
    · have hlt : a < s.bumpIndex := by
        have hne : a.toNat ≠ s.bumpIndex.toNat := fun heq => hab (UInt64.toNat_inj.mp heq)
        show a.toNat < s.bumpIndex.toNat; omega
      obtain ⟨hl, hr, hp, hc⟩ := hwf_nodes.2.2.2.2.2 a ha0 hlt
      have hbump_succ : s.bumpIndex < s.bumpIndex + 1 := by
        rw [UInt64.lt_iff_toNat_lt]; omega
      exact ⟨u64_le_trans hl (u64_le_of_lt hbump_succ), u64_le_trans hr (u64_le_of_lt hbump_succ),
        u64_le_trans hp (u64_le_of_lt hbump_succ), hc⟩

theorem insertAt_linked_wf_free (s : State) (parentAddress direction k v : UInt64)
    (hwf : wf s) (hsize : s.size.toNat < 4)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hfresh : s.freeHead ≠ s.bumpIndex) (he0 : s.freeHead ≠ 0) (hf4 : s.freeHead < 5) :
    wf (insertAtLinkedFree s parentAddress direction k v) := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have hwf' : wf s := ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩
  have hfblt : s.freeHead < s.bumpIndex := by
    rw [UInt64.lt_iff_toNat_lt]
    have hfb' : s.freeHead.toNat ≤ s.bumpIndex.toNat := (UInt64.le_iff_toNat_le).1 hfb
    have hne : s.freeHead.toNat ≠ s.bumpIndex.toNat := fun heq => hfresh (UInt64.toNat_inj.mp heq)
    omega
  have hwf_nodes := insertAt_linked_nodes_wf s parentAddress direction s.freeHead k v hwf' hparent
    (u64_le_of_lt hfblt)
  have hfh : (1 : UInt64) ≤ s.freeHead := by
    rw [UInt64.le_iff_toNat_le]
    exact Nat.one_le_iff_ne_zero.mpr (fun heq => he0 (UInt64.toNat_inj.mp heq))
  have hptr' := hptr s.freeHead hfh hfblt
  obtain ⟨hl, _, _, _⟩ := hptr'
  unfold insertAtLinkedFree
  dsimp only
  refine ⟨?_, hb1, hb5, ?_, hl, ?_⟩
  · show (s.size + 1).toNat ≤ 4
    have hst : s.size.toNat < 4 := hsize
    rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
    omega
  · show (s.nodes[(s.freeHead.toNat - 1) % 4]!.left.toNat ≤ 5)
    rw [UInt64.le_iff_toNat_le] at hl
    have hb5' : s.bumpIndex.toNat ≤ 5 := (UInt64.le_iff_toNat_le).1 hb5
    omega
  · intro a ha0 ha1
    by_cases hab : a = s.freeHead
    · rw [hab]
      have hget := vec_set2_get_right s.nodes ((parentAddress.toNat - 1) % 4)
        ((s.freeHead.toNat - 1) % 4)
        (if direction = 0 then { s.nodes[(parentAddress.toNat - 1) % 4]! with left := s.freeHead }
          else { s.nodes[(parentAddress.toNat - 1) % 4]! with right := s.freeHead })
        { left := 0, right := 0, parent := parentAddress, color := 1, key := k, value := v }
        (by omega) (by omega)
      rw [hget]
      exact ⟨Nat.zero_le _, Nat.zero_le _, u64_le_of_lt hparent.2, (by decide : (1 : UInt64) ≤ 1)⟩
    · exact hwf_nodes.2.2.2.2.2 a ha0 ha1

theorem insertAt_linked_wf (s : State) (parentAddress direction k v : UInt64)
    (hwf : wf s) (hsize : s.size.toNat < 4)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hvalid :
      (s.freeHead = s.bumpIndex ∧ s.bumpIndex ≠ 0 ∧ s.bumpIndex < 5) ∨
        (s.freeHead ≠ s.bumpIndex ∧ s.freeHead ≠ 0 ∧ s.freeHead < 5)) :
    wf (if s.freeHead = s.bumpIndex then insertAtLinkedBump s parentAddress direction k v
        else insertAtLinkedFree s parentAddress direction k v) := by
  rcases hvalid with hBump | hFree
  · simp only [(hBump.1)]
    exact insertAt_linked_wf_bump s parentAddress direction k v hwf hsize hparent hBump.2.1 hBump.2.2 hBump.1
  · simp only [if_neg hFree.1]
    exact insertAt_linked_wf_free s parentAddress direction k v hwf hsize hparent hFree.1 hFree.2.1 hFree.2.2

theorem insertAt_wf (s : State) (parentAddress direction k v : UInt64) {t : State} {a : UInt64}
    (h : insertAt s parentAddress direction k v = .ok (t, a)) (hwf : wf s)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hparentBlack : s.nodes[(parentAddress.toNat - 1) % 4]!.color ≠ 1) :
    wf t := by
  unfold insertAt at h
  split at h
  · rename_i hsz4
    by_cases hfbeq : s.freeHead = s.bumpIndex
    · simp only [hfbeq, ↓reduceIte] at h
      by_cases hb0 : s.bumpIndex = 0
      · simp [hb0] at h
      · by_cases hb4 : s.bumpIndex < 5
        · simp only [hb0, hb4, ↓reduceIte] at h
          unfold fixInserted at h
          by_cases hred : s.nodes[(parentAddress.toNat - 1) % 4]!.color = 1
          · exact absurd hred hparentBlack
          · simp only [if_neg hred] at h
            obtain ⟨rfl, rfl⟩ := h
            exact insertAt_linked_wf_bump s parentAddress direction k v hwf hsz4 hparent hb0 hb4 hfbeq
        · simp [hb4] at h
    · simp only [if_neg hfbeq, ↓reduceIte] at h
      by_cases he0 : s.freeHead = 0
      · simp [he0] at h
      · by_cases hf4 : s.freeHead < 5
        · simp only [he0, hf4, ↓reduceIte] at h
          unfold fixInserted at h
          by_cases hred : s.nodes[(parentAddress.toNat - 1) % 4]!.color = 1
          · exact absurd hred hparentBlack
          · simp only [if_neg hred] at h
            obtain ⟨rfl, rfl⟩ := h
            exact insertAt_linked_wf_free s parentAddress direction k v hwf hsz4 hparent hfbeq he0 hf4
        · simp [hf4] at h
  · simp at h

/-- 三槽只把 `color` 涂成 0：几何指针不变，经 `wf_nodes_set3` 闭包。
`fixInserted` 红叔 recolor 分支的公共核。 -/
private theorem paint3_black_wf (s : State) (p u g : UInt64) (hwf : wf s)
    (hp : 1 ≤ p ∧ p < s.bumpIndex) (hu : 1 ≤ u ∧ u < s.bumpIndex)
    (hg : 1 ≤ g ∧ g < s.bumpIndex) :
    wf { s with
      nodes :=
        let pIdx := (p.toNat - 1) % 4
        let uIdx := (u.toNat - 1) % 4
        let gIdx := (g.toNat - 1) % 4
        ((s.nodes.set pIdx { s.nodes[pIdx]! with color := 0 }).set
          uIdx { s.nodes[uIdx]! with color := 0 }).set
          gIdx { s.nodes[gIdx]! with color := 0 } } := by
  have hpn := hwf.2.2.2.2.2 p hp.1 hp.2
  have hun := hwf.2.2.2.2.2 u hu.1 hu.2
  have hgn := hwf.2.2.2.2.2 g hg.1 hg.2
  apply wf_nodes_set3 s ((p.toNat - 1) % 4) ((u.toNat - 1) % 4) ((g.toNat - 1) % 4)
    { s.nodes[(p.toNat - 1) % 4]! with color := 0 }
    { s.nodes[(u.toNat - 1) % 4]! with color := 0 }
    { s.nodes[(g.toNat - 1) % 4]! with color := 0 }
    (by omega) (by omega) (by omega) hwf
  · exact ⟨hpn.1, hpn.2.1, hpn.2.2.1, (by decide : (0 : UInt64) ≤ 1)⟩
  · exact ⟨hun.1, hun.2.1, hun.2.2.1, (by decide : (0 : UInt64) ≤ 1)⟩
  · exact ⟨hgn.1, hgn.2.1, hgn.2.2.1, (by decide : (0 : UInt64) ≤ 1)⟩

/-- **fixInserted grand=0 涂父黑**：红父且祖父地址为 0（父即 root）时，
只把 linked 态 `s` 上父槽 `color := 0`；几何指针不变，经 `wf_nodes_set`。 -/
theorem fixInserted_grand0_paint_parent_wf
    (before s : State) (nodeAddress parentAddress direction : UInt64)
    {t : State} {ret : UInt64}
    (h : fixInserted before s nodeAddress parentAddress direction = .ok (t, ret))
    (hwf : wf s)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hparentRed : before.nodes[(parentAddress.toNat - 1) % 4]!.color = 1)
    (hgrand0 : before.nodes[(parentAddress.toNat - 1) % 4]!.parent = 0) :
    wf t := by
  unfold fixInserted at h
  simp only [hparentRed, ↓reduceIte] at h
  simp only [hgrand0, ↓reduceIte] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hpn := hwf.2.2.2.2.2 parentAddress hparent.1 hparent.2
  apply wf_nodes_set s ((parentAddress.toNat - 1) % 4)
    { s.nodes[(parentAddress.toNat - 1) % 4]! with color := 0 } (by omega) hwf
  · exact hpn.1
  · exact hpn.2.1
  · exact hpn.2.2.1
  · exact (by decide : (0 : UInt64) ≤ 1)

/-- **fixInserted 红叔 recolor（父为祖父左子）**：控制流读 `before`，
写回只改 linked 态 `s` 上父/叔/祖三槽 `color := 0`。 -/
theorem fixInserted_recolor_left_uncle_wf
    (before s : State) (nodeAddress parentAddress direction : UInt64)
    {t : State} {ret : UInt64}
    (h : fixInserted before s nodeAddress parentAddress direction = .ok (t, ret))
    (hwf : wf s)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hparentRed : before.nodes[(parentAddress.toNat - 1) % 4]!.color = 1)
    (hgrandNe : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0)
    (hgrand : 1 ≤ before.nodes[(parentAddress.toNat - 1) % 4]!.parent ∧
      before.nodes[(parentAddress.toNat - 1) % 4]!.parent < s.bumpIndex)
    (hleft :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left =
        parentAddress)
    (huncle :
      let grandAddress := before.nodes[(parentAddress.toNat - 1) % 4]!.parent
      let uncleAddress := before.nodes[(grandAddress.toNat - 1) % 4]!.right
      uncleAddress ≠ 0 ∧ 1 ≤ uncleAddress ∧ uncleAddress < s.bumpIndex ∧
        before.nodes[(uncleAddress.toNat - 1) % 4]!.color = 1) :
    wf t := by
  unfold fixInserted at h
  simp only [hparentRed, ↓reduceIte] at h
  have hgrandNe' : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0 := hgrandNe
  simp only [if_neg hgrandNe', ↓reduceIte] at h
  have hleft' :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left =
        parentAddress := hleft
  simp only [hleft', ↓reduceIte] at h
  have huncleNe :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.right ≠ 0 :=
    huncle.1
  have huncleRed :
      before.nodes[(before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) %
          4]!.right.toNat - 1) % 4]!.color = 1 := huncle.2.2.2
  have huncleColor :
      (if before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.right = 0
        then (0 : UInt64)
        else
          before.nodes[(before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) %
              4]!.right.toNat - 1) % 4]!.color) = 1 := by
    simp only [if_neg huncleNe, huncleRed]
  simp only [huncleColor, ↓reduceIte] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact paint3_black_wf s parentAddress
    (before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.right)
    (before.nodes[(parentAddress.toNat - 1) % 4]!.parent) hwf hparent
    ⟨huncle.2.1, huncle.2.2.1⟩ hgrand

/-- **fixInserted 红叔 recolor（父为祖父右子）**：与 `fixInserted_recolor_left_uncle_wf`
镜像——控制流读 `before`，写回只改 linked 态 `s` 上父/叔/祖三槽 `color := 0`。 -/
theorem fixInserted_recolor_right_uncle_wf
    (before s : State) (nodeAddress parentAddress direction : UInt64)
    {t : State} {ret : UInt64}
    (h : fixInserted before s nodeAddress parentAddress direction = .ok (t, ret))
    (hwf : wf s)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hparentRed : before.nodes[(parentAddress.toNat - 1) % 4]!.color = 1)
    (hgrandNe : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0)
    (hgrand : 1 ≤ before.nodes[(parentAddress.toNat - 1) % 4]!.parent ∧
      before.nodes[(parentAddress.toNat - 1) % 4]!.parent < s.bumpIndex)
    (hright :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left ≠
        parentAddress)
    (huncle :
      let grandAddress := before.nodes[(parentAddress.toNat - 1) % 4]!.parent
      let uncleAddress := before.nodes[(grandAddress.toNat - 1) % 4]!.left
      uncleAddress ≠ 0 ∧ 1 ≤ uncleAddress ∧ uncleAddress < s.bumpIndex ∧
        before.nodes[(uncleAddress.toNat - 1) % 4]!.color = 1) :
    wf t := by
  unfold fixInserted at h
  simp only [hparentRed, ↓reduceIte] at h
  have hgrandNe' : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0 := hgrandNe
  simp only [if_neg hgrandNe', ↓reduceIte] at h
  have hright' :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left ≠
        parentAddress := hright
  simp only [if_neg hright', ↓reduceIte] at h
  have huncleNe :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left ≠ 0 :=
    huncle.1
  have huncleRed :
      before.nodes[(before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) %
          4]!.left.toNat - 1) % 4]!.color = 1 := huncle.2.2.2
  have huncleColor :
      (if before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left = 0
        then (0 : UInt64)
        else
          before.nodes[(before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) %
              4]!.left.toNat - 1) % 4]!.color) = 1 := by
    simp only [if_neg huncleNe, huncleRed]
  simp only [huncleColor, ↓reduceIte] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact paint3_black_wf s parentAddress
    (before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left)
    (before.nodes[(parentAddress.toNat - 1) % 4]!.parent) hwf hparent
    ⟨huncle.2.1, huncle.2.2.1⟩ hgrand

/-- **fixInserted LL 旋转（父为祖父左子 + 黑叔 + direction≠1）**：
控制流读 `before`，写回改 linked 态 `s` 上祖/父两槽（祖：`left:=0`/`parent:=父`/`color:=1`；
父：`right:=祖`/`parent:=0`/`color:=0`）并把 `root` 设为父。
几何 `wf` 经 `wf_nodes_set2`（`root` 不在谓词内）。
`fixInserted` 在此有界切片内联「祖父即原 root」的右旋，**未**调用
`rotateRight`；故直接复用 `wf_nodes_set2` 而非 `rotateRight_wf`
（后者面向通用 `rotateRight` 成功路径与更宽父挂接分支）。 -/
theorem fixInserted_ll_wf
    (before s : State) (nodeAddress parentAddress direction : UInt64)
    {t : State} {ret : UInt64}
    (h : fixInserted before s nodeAddress parentAddress direction = .ok (t, ret))
    (hwf : wf s)
    (hparent : 1 ≤ parentAddress ∧ parentAddress < s.bumpIndex)
    (hparentRed : before.nodes[(parentAddress.toNat - 1) % 4]!.color = 1)
    (hgrandNe : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0)
    (hgrand : 1 ≤ before.nodes[(parentAddress.toNat - 1) % 4]!.parent ∧
      before.nodes[(parentAddress.toNat - 1) % 4]!.parent < s.bumpIndex)
    (hleft :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left =
        parentAddress)
    (huncleBlack :
      let grandAddress := before.nodes[(parentAddress.toNat - 1) % 4]!.parent
      let uncleAddress := before.nodes[(grandAddress.toNat - 1) % 4]!.right
      (if uncleAddress = 0 then (0 : UInt64)
        else before.nodes[(uncleAddress.toNat - 1) % 4]!.color) ≠ 1)
    (hdir : direction ≠ 1) :
    wf t := by
  unfold fixInserted at h
  simp only [hparentRed, ↓reduceIte] at h
  have hgrandNe' : before.nodes[(parentAddress.toNat - 1) % 4]!.parent ≠ 0 := hgrandNe
  simp only [if_neg hgrandNe', ↓reduceIte] at h
  have hleft' :
      before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.left =
        parentAddress := hleft
  simp only [hleft', ↓reduceIte] at h
  have huncleBlack' :
      (if before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]!.right = 0
        then (0 : UInt64)
        else
          before.nodes[(before.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) %
              4]!.right.toNat - 1) % 4]!.color) ≠ 1 := huncleBlack
  simp only [if_neg huncleBlack', ↓reduceIte] at h
  simp only [if_neg hdir, ↓reduceIte] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hpn := hwf.2.2.2.2.2 parentAddress hparent.1 hparent.2
  have hgn := hwf.2.2.2.2.2
    (before.nodes[(parentAddress.toNat - 1) % 4]!.parent) hgrand.1 hgrand.2
  apply wf_nodes_set2 s
    ((before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4)
    ((parentAddress.toNat - 1) % 4)
    { s.nodes[(before.nodes[(parentAddress.toNat - 1) % 4]!.parent.toNat - 1) % 4]! with
      left := 0
      parent := parentAddress
      color := 1 }
    { s.nodes[(parentAddress.toNat - 1) % 4]! with
      right := before.nodes[(parentAddress.toNat - 1) % 4]!.parent
      parent := 0
      color := 0 }
    (by omega) (by omega) hwf
  · exact ⟨Nat.zero_le _, hgn.2.1, u64_le_of_lt hparent.2, (by decide : (1 : UInt64) ≤ 1)⟩
  · exact ⟨hpn.1, u64_le_of_lt hgrand.2, Nat.zero_le _, (by decide : (0 : UInt64) ≤ 1)⟩

theorem rotateLeft_wf (s : State) (xAddress : UInt64) {t : State} {y : UInt64}
    (h : rotateLeft s xAddress = .ok (t, y)) (hwf : wf s)
    (hx : 1 ≤ xAddress ∧ xAddress < s.bumpIndex)
    (hyBound : ∃ yAddr, s.nodes[xAddress.toNat - 1]!.right = yAddr ∧
      1 ≤ yAddr ∧ yAddr < s.bumpIndex)
    (hInnerBound : ∀ yAddr, s.nodes[xAddress.toNat - 1]!.right = yAddr →
      s.nodes[yAddr.toNat - 1]!.left = 0 ∨
        (1 ≤ s.nodes[yAddr.toNat - 1]!.left ∧ s.nodes[yAddr.toNat - 1]!.left < s.bumpIndex))
    (hParentBound : s.nodes[xAddress.toNat - 1]!.parent = 0 ∨
      (1 ≤ s.nodes[xAddress.toNat - 1]!.parent ∧
        s.nodes[xAddress.toNat - 1]!.parent < s.bumpIndex)) :
    wf t := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨yAddress, hyEq, hy0, hy1⟩ := hyBound
  have hInner := hInnerBound yAddress hyEq
  have hxne : xAddress ≠ 0 := by
    intro heq; rw [heq] at hx0; exact absurd hx0 (by decide)
  have hbi5 : s.bumpIndex.toNat ≤ 5 := hwf.2.2.1
  have hxi4 : xAddress.toNat - 1 < 4 := by
    have h1 : xAddress.toNat < s.bumpIndex.toNat := hx1
    omega
  have hyne : yAddress ≠ 0 := by
    intro heq; rw [heq] at hy0; exact absurd hy0 (by decide)
  have hyi4 : yAddress.toNat - 1 < 4 := by
    have h1 : yAddress.toNat < s.bumpIndex.toNat := hy1
    omega
  have hyne_raw : s.nodes[xAddress.toNat - 1]!.right ≠ 0 := by rw [hyEq]; exact hyne
  have hyi4_raw : s.nodes[xAddress.toNat - 1]!.right.toNat - 1 < 4 := by rw [hyEq]; exact hyi4
  have hptr := hwf.2.2.2.2.2
  have hxnode := hptr xAddress hx0 hx1
  have hynode := hptr yAddress hy0 hy1
  have hxmod : (xAddress.toNat - 1) % 4 = xAddress.toNat - 1 := Nat.mod_eq_of_lt hxi4
  have hymod : (yAddress.toNat - 1) % 4 = yAddress.toNat - 1 := Nat.mod_eq_of_lt hyi4
  rw [hxmod] at hxnode
  rw [hymod] at hynode
  have hinner4 : ¬ (4 < s.nodes[yAddress.toNat - 1]!.left) := by
    intro hc
    rcases hInner with h0 | ⟨h1, h2⟩
    · rw [h0] at hc; exact absurd hc (by decide)
    · have hc' : (4 : UInt64).toNat < (s.nodes[yAddress.toNat - 1]!.left).toNat := hc
      have h2' : (s.nodes[yAddress.toNat - 1]!.left).toNat < s.bumpIndex.toNat := h2
      have h4 : (4 : UInt64).toNat = 4 := rfl
      omega
  have hparent4 : ¬ (4 < s.nodes[xAddress.toNat - 1]!.parent) := by
    intro hc
    rcases hParentBound with h0 | ⟨h1, h2⟩
    · rw [h0] at hc; exact absurd hc (by decide)
    · have hc' : (4 : UInt64).toNat < (s.nodes[xAddress.toNat - 1]!.parent).toNat := hc
      have h2' : (s.nodes[xAddress.toNat - 1]!.parent).toNat < s.bumpIndex.toNat := h2
      have h4 : (4 : UInt64).toNat = 4 := rfl
      omega
  unfold rotateLeft at h
  rw [if_neg hxne] at h
  simp only [hxi4, ↓reduceDIte] at h
  rw [if_neg hyne_raw] at h
  simp only [hyi4_raw, ↓reduceDIte] at h
  simp only [hyEq] at h
  rw [if_neg hinner4, if_neg hparent4] at h
  split at h
  · rename_i hInner0
    split at h
    · rename_i hParent0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb1 : s.nodes[xAddress.toNat - 1]!.left ≤ s.bumpIndex ∧
          s.nodes[yAddress.toNat - 1]!.left ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
        ⟨hxnode.1, by rw [hInner0]; exact Nat.zero_le _, u64_le_of_lt hy1, hxnode.2.2.2⟩
      have hb2 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[xAddress.toNat - 1]!.left, right := s.nodes[yAddress.toNat - 1]!.left,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
      apply wf_nodes_set2 s (xAddress.toNat - 1) (yAddress.toNat - 1) _ _ hxi4 hyi4 hwf hb1
      exact ⟨u64_le_of_lt hx1, hb2.2.1, Nat.zero_le _, hb2.2.2.2⟩
    · rename_i hParentNe
      have hParentPos := hParentBound.resolve_left hParentNe
      have hparentnode := hptr s.nodes[xAddress.toNat - 1]!.parent hParentPos.1 hParentPos.2
      have hparentIdx4 : (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4 < 4 := by omega
      have hb1 : s.nodes[xAddress.toNat - 1]!.left ≤ s.bumpIndex ∧
          s.nodes[yAddress.toNat - 1]!.left ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
        ⟨hxnode.1, by rw [hInner0]; exact Nat.zero_le _, u64_le_of_lt hy1, hxnode.2.2.2⟩
      have hb2 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[xAddress.toNat - 1]!.left, right := s.nodes[yAddress.toNat - 1]!.left,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) hparentIdx4 hparentnode
      have hb3 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[xAddress.toNat - 1]!.left, right := s.nodes[yAddress.toNat - 1]!.left,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
      split at h
      · rename_i hLeftChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set3 s (xAddress.toNat - 1)
          ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) (yAddress.toNat - 1) _ _ _
          hxi4 hparentIdx4 hyi4 hwf hb1
        · exact ⟨u64_le_of_lt hy1, hb2.2.1, hb2.2.2.1, hb2.2.2.2⟩
        · exact ⟨u64_le_of_lt hx1, hb3.2.1, u64_le_of_lt hParentPos.2, hb3.2.2.2⟩
      · rename_i hRightChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set3 s (xAddress.toNat - 1)
          ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) (yAddress.toNat - 1) _ _ _
          hxi4 hparentIdx4 hyi4 hwf hb1
        · exact ⟨hb2.1, u64_le_of_lt hy1, hb2.2.2.1, hb2.2.2.2⟩
        · exact ⟨u64_le_of_lt hx1, hb3.2.1, u64_le_of_lt hParentPos.2, hb3.2.2.2⟩
  · rename_i hInnerNe
    have hInnerPos := hInner.resolve_left hInnerNe
    have hinnernode := hptr s.nodes[yAddress.toNat - 1]!.left hInnerPos.1 hInnerPos.2
    have hinnerIdx4 : (s.nodes[yAddress.toNat - 1]!.left.toNat - 1) % 4 < 4 := by omega
    have hb1 : s.nodes[xAddress.toNat - 1]!.left ≤ s.bumpIndex ∧
        s.nodes[yAddress.toNat - 1]!.left ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
        s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
      ⟨hxnode.1, u64_le_of_lt hInnerPos.2, u64_le_of_lt hy1, hxnode.2.2.2⟩
    let n1 : Node := { s.nodes[xAddress.toNat - 1]! with
      right := s.nodes[yAddress.toNat - 1]!.left, parent := yAddress }
    let nodes1 : Vector Node 4 := s.nodes.set (xAddress.toNat - 1) n1 hxi4
    let innerIndex : Nat := (s.nodes[yAddress.toNat - 1]!.left.toNat - 1) % 4
    let n2 : Node := { nodes1[innerIndex]! with parent := xAddress }
    have hbInner1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 innerIndex hinnerIdx4
      hinnernode
    have hbN2 : n2.left ≤ s.bumpIndex ∧ n2.right ≤ s.bumpIndex ∧ n2.parent ≤ s.bumpIndex ∧
        n2.color ≤ 1 :=
      ⟨hbInner1.1, hbInner1.2.1, u64_le_of_lt hx1, hbInner1.2.2.2⟩
    have hbY1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
    have hbY2 := node_bound_set ({ s with nodes := nodes1 }) innerIndex n2 hinnerIdx4 hbN2
      (yAddress.toNat - 1) hyi4 hbY1
    split at h
    · rename_i hParent0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply wf_nodes_set3 s (xAddress.toNat - 1) innerIndex (yAddress.toNat - 1) n1 n2 _
        hxi4 hinnerIdx4 hyi4 hwf hb1 hbN2
      exact ⟨u64_le_of_lt hx1, hbY2.2.1, Nat.zero_le _, hbY2.2.2.2⟩
    · rename_i hParentNe
      have hParentPos := hParentBound.resolve_left hParentNe
      have hparentnode := hptr s.nodes[xAddress.toNat - 1]!.parent hParentPos.1 hParentPos.2
      have hparentIdx4 : (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4 < 4 := by omega
      let parentIndex : Nat := (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4
      have hparentnode1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 parentIndex
        hparentIdx4 hparentnode
      have hparentnode2 := node_bound_set ({ s with nodes := nodes1 }) innerIndex n2 hinnerIdx4
        hbN2 parentIndex hparentIdx4 hparentnode1
      split at h
      · rename_i hLeftChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set4 s (xAddress.toNat - 1) innerIndex parentIndex (yAddress.toNat - 1)
          n1 n2 _ _ hxi4 hinnerIdx4 hparentIdx4 hyi4 hwf hb1 hbN2
        · exact ⟨u64_le_of_lt hy1, hparentnode2.2.1, hparentnode2.2.2.1, hparentnode2.2.2.2⟩
        · exact ⟨u64_le_of_lt hx1, hbY2.2.1, u64_le_of_lt hParentPos.2, hbY2.2.2.2⟩
      · rename_i hRightChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set4 s (xAddress.toNat - 1) innerIndex parentIndex (yAddress.toNat - 1)
          n1 n2 _ _ hxi4 hinnerIdx4 hparentIdx4 hyi4 hwf hb1 hbN2
        · exact ⟨hparentnode2.1, u64_le_of_lt hy1, hparentnode2.2.2.1, hparentnode2.2.2.2⟩
        · exact ⟨u64_le_of_lt hx1, hbY2.2.1, u64_le_of_lt hParentPos.2, hbY2.2.2.2⟩

/-- `rotateRight` 保持几何 `wf`：与 `rotateLeft_wf` 镜像（`left`/`right` 互换），
BST 有序性仍留给后续切片。 -/
theorem rotateRight_wf (s : State) (xAddress : UInt64) {t : State} {y : UInt64}
    (h : rotateRight s xAddress = .ok (t, y)) (hwf : wf s)
    (hx : 1 ≤ xAddress ∧ xAddress < s.bumpIndex)
    (hyBound : ∃ yAddr, s.nodes[xAddress.toNat - 1]!.left = yAddr ∧
      1 ≤ yAddr ∧ yAddr < s.bumpIndex)
    (hInnerBound : ∀ yAddr, s.nodes[xAddress.toNat - 1]!.left = yAddr →
      s.nodes[yAddr.toNat - 1]!.right = 0 ∨
        (1 ≤ s.nodes[yAddr.toNat - 1]!.right ∧ s.nodes[yAddr.toNat - 1]!.right < s.bumpIndex))
    (hParentBound : s.nodes[xAddress.toNat - 1]!.parent = 0 ∨
      (1 ≤ s.nodes[xAddress.toNat - 1]!.parent ∧
        s.nodes[xAddress.toNat - 1]!.parent < s.bumpIndex)) :
    wf t := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨yAddress, hyEq, hy0, hy1⟩ := hyBound
  have hInner := hInnerBound yAddress hyEq
  have hxne : xAddress ≠ 0 := by
    intro heq; rw [heq] at hx0; exact absurd hx0 (by decide)
  have hbi5 : s.bumpIndex.toNat ≤ 5 := hwf.2.2.1
  have hxi4 : xAddress.toNat - 1 < 4 := by
    have h1 : xAddress.toNat < s.bumpIndex.toNat := hx1
    omega
  have hyne : yAddress ≠ 0 := by
    intro heq; rw [heq] at hy0; exact absurd hy0 (by decide)
  have hyi4 : yAddress.toNat - 1 < 4 := by
    have h1 : yAddress.toNat < s.bumpIndex.toNat := hy1
    omega
  have hyne_raw : s.nodes[xAddress.toNat - 1]!.left ≠ 0 := by rw [hyEq]; exact hyne
  have hyi4_raw : s.nodes[xAddress.toNat - 1]!.left.toNat - 1 < 4 := by rw [hyEq]; exact hyi4
  have hptr := hwf.2.2.2.2.2
  have hxnode := hptr xAddress hx0 hx1
  have hynode := hptr yAddress hy0 hy1
  have hxmod : (xAddress.toNat - 1) % 4 = xAddress.toNat - 1 := Nat.mod_eq_of_lt hxi4
  have hymod : (yAddress.toNat - 1) % 4 = yAddress.toNat - 1 := Nat.mod_eq_of_lt hyi4
  rw [hxmod] at hxnode
  rw [hymod] at hynode
  have hinner4 : ¬ (4 < s.nodes[yAddress.toNat - 1]!.right) := by
    intro hc
    rcases hInner with h0 | ⟨h1, h2⟩
    · rw [h0] at hc; exact absurd hc (by decide)
    · have hc' : (4 : UInt64).toNat < (s.nodes[yAddress.toNat - 1]!.right).toNat := hc
      have h2' : (s.nodes[yAddress.toNat - 1]!.right).toNat < s.bumpIndex.toNat := h2
      have h4 : (4 : UInt64).toNat = 4 := rfl
      omega
  have hparent4 : ¬ (4 < s.nodes[xAddress.toNat - 1]!.parent) := by
    intro hc
    rcases hParentBound with h0 | ⟨h1, h2⟩
    · rw [h0] at hc; exact absurd hc (by decide)
    · have hc' : (4 : UInt64).toNat < (s.nodes[xAddress.toNat - 1]!.parent).toNat := hc
      have h2' : (s.nodes[xAddress.toNat - 1]!.parent).toNat < s.bumpIndex.toNat := h2
      have h4 : (4 : UInt64).toNat = 4 := rfl
      omega
  unfold rotateRight at h
  rw [if_neg hxne] at h
  simp only [hxi4, ↓reduceDIte] at h
  rw [if_neg hyne_raw] at h
  simp only [hyi4_raw, ↓reduceDIte] at h
  simp only [hyEq] at h
  rw [if_neg hinner4, if_neg hparent4] at h
  split at h
  · rename_i hInner0
    split at h
    · rename_i hParent0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb1 : s.nodes[yAddress.toNat - 1]!.right ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.right ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
        ⟨by rw [hInner0]; exact Nat.zero_le _, hxnode.2.1, u64_le_of_lt hy1, hxnode.2.2.2⟩
      have hb2 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[yAddress.toNat - 1]!.right,
          right := s.nodes[xAddress.toNat - 1]!.right,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
      apply wf_nodes_set2 s (xAddress.toNat - 1) (yAddress.toNat - 1) _ _ hxi4 hyi4 hwf hb1
      exact ⟨hb2.1, u64_le_of_lt hx1, Nat.zero_le _, hb2.2.2.2⟩
    · rename_i hParentNe
      have hParentPos := hParentBound.resolve_left hParentNe
      have hparentnode := hptr s.nodes[xAddress.toNat - 1]!.parent hParentPos.1 hParentPos.2
      have hparentIdx4 : (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4 < 4 := by omega
      have hb1 : s.nodes[yAddress.toNat - 1]!.right ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.right ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
          s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
        ⟨by rw [hInner0]; exact Nat.zero_le _, hxnode.2.1, u64_le_of_lt hy1, hxnode.2.2.2⟩
      have hb2 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[yAddress.toNat - 1]!.right,
          right := s.nodes[xAddress.toNat - 1]!.right,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) hparentIdx4 hparentnode
      have hb3 := node_bound_set s (xAddress.toNat - 1)
        { left := s.nodes[yAddress.toNat - 1]!.right,
          right := s.nodes[xAddress.toNat - 1]!.right,
          parent := yAddress, color := s.nodes[xAddress.toNat - 1]!.color,
          key := s.nodes[xAddress.toNat - 1]!.key, value := s.nodes[xAddress.toNat - 1]!.value }
        hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
      split at h
      · rename_i hLeftChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set3 s (xAddress.toNat - 1)
          ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) (yAddress.toNat - 1) _ _ _
          hxi4 hparentIdx4 hyi4 hwf hb1
        · exact ⟨u64_le_of_lt hy1, hb2.2.1, hb2.2.2.1, hb2.2.2.2⟩
        · exact ⟨hb3.1, u64_le_of_lt hx1, u64_le_of_lt hParentPos.2, hb3.2.2.2⟩
      · rename_i hRightChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set3 s (xAddress.toNat - 1)
          ((s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4) (yAddress.toNat - 1) _ _ _
          hxi4 hparentIdx4 hyi4 hwf hb1
        · exact ⟨hb2.1, u64_le_of_lt hy1, hb2.2.2.1, hb2.2.2.2⟩
        · exact ⟨hb3.1, u64_le_of_lt hx1, u64_le_of_lt hParentPos.2, hb3.2.2.2⟩
  · rename_i hInnerNe
    have hInnerPos := hInner.resolve_left hInnerNe
    have hinnernode := hptr s.nodes[yAddress.toNat - 1]!.right hInnerPos.1 hInnerPos.2
    have hinnerIdx4 : (s.nodes[yAddress.toNat - 1]!.right.toNat - 1) % 4 < 4 := by omega
    have hb1 : s.nodes[yAddress.toNat - 1]!.right ≤ s.bumpIndex ∧
        s.nodes[xAddress.toNat - 1]!.right ≤ s.bumpIndex ∧ yAddress ≤ s.bumpIndex ∧
        s.nodes[xAddress.toNat - 1]!.color ≤ 1 :=
      ⟨u64_le_of_lt hInnerPos.2, hxnode.2.1, u64_le_of_lt hy1, hxnode.2.2.2⟩
    let n1 : Node := { s.nodes[xAddress.toNat - 1]! with
      left := s.nodes[yAddress.toNat - 1]!.right, parent := yAddress }
    let nodes1 : Vector Node 4 := s.nodes.set (xAddress.toNat - 1) n1 hxi4
    let innerIndex : Nat := (s.nodes[yAddress.toNat - 1]!.right.toNat - 1) % 4
    let n2 : Node := { nodes1[innerIndex]! with parent := xAddress }
    have hbInner1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 innerIndex hinnerIdx4
      hinnernode
    have hbN2 : n2.left ≤ s.bumpIndex ∧ n2.right ≤ s.bumpIndex ∧ n2.parent ≤ s.bumpIndex ∧
        n2.color ≤ 1 :=
      ⟨hbInner1.1, hbInner1.2.1, u64_le_of_lt hx1, hbInner1.2.2.2⟩
    have hbY1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 (yAddress.toNat - 1) hyi4 hynode
    have hbY2 := node_bound_set ({ s with nodes := nodes1 }) innerIndex n2 hinnerIdx4 hbN2
      (yAddress.toNat - 1) hyi4 hbY1
    split at h
    · rename_i hParent0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply wf_nodes_set3 s (xAddress.toNat - 1) innerIndex (yAddress.toNat - 1) n1 n2 _
        hxi4 hinnerIdx4 hyi4 hwf hb1 hbN2
      exact ⟨hbY2.1, u64_le_of_lt hx1, Nat.zero_le _, hbY2.2.2.2⟩
    · rename_i hParentNe
      have hParentPos := hParentBound.resolve_left hParentNe
      have hparentnode := hptr s.nodes[xAddress.toNat - 1]!.parent hParentPos.1 hParentPos.2
      have hparentIdx4 : (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4 < 4 := by omega
      let parentIndex : Nat := (s.nodes[xAddress.toNat - 1]!.parent.toNat - 1) % 4
      have hparentnode1 := node_bound_set s (xAddress.toNat - 1) n1 hxi4 hb1 parentIndex
        hparentIdx4 hparentnode
      have hparentnode2 := node_bound_set ({ s with nodes := nodes1 }) innerIndex n2 hinnerIdx4
        hbN2 parentIndex hparentIdx4 hparentnode1
      split at h
      · rename_i hLeftChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set4 s (xAddress.toNat - 1) innerIndex parentIndex (yAddress.toNat - 1)
          n1 n2 _ _ hxi4 hinnerIdx4 hparentIdx4 hyi4 hwf hb1 hbN2
        · exact ⟨u64_le_of_lt hy1, hparentnode2.2.1, hparentnode2.2.2.1, hparentnode2.2.2.2⟩
        · exact ⟨hbY2.1, u64_le_of_lt hx1, u64_le_of_lt hParentPos.2, hbY2.2.2.2⟩
      · rename_i hRightChild
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply wf_nodes_set4 s (xAddress.toNat - 1) innerIndex parentIndex (yAddress.toNat - 1)
          n1 n2 _ _ hxi4 hinnerIdx4 hparentIdx4 hyi4 hwf hb1 hbN2
        · exact ⟨hparentnode2.1, u64_le_of_lt hy1, hparentnode2.2.2.1, hparentnode2.2.2.2⟩
        · exact ⟨hbY2.1, u64_le_of_lt hx1, u64_le_of_lt hParentPos.2, hbY2.2.2.2⟩

end Proofs

end Examples.Svm.Tree
