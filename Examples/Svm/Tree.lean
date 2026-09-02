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

/-! ### 良构谓词（WF）与 sf-011 全树保持

几何 `wf`（p-004）：分配器游标 + 已分配槽的 left/right/parent/color 有界。

sf-011 在其上补三层可陈述结构（均在 N=4 燃料下；不引入无界谓词）：

* `reachable` — 从 root 沿 left/right 至多 3 步可达
* `parentInv` — 可达节点的孩子回指该父（父子互逆）
* `bstLocal` — 可达节点的直接孩子满足局部 key 序

颜色：`wf` 已钉 `color ≤ 1`；根黑由 `rootBlack` 陈述。索引层合同见
`ProofForge.Svm.Sdk.OrderedMapModel`（sf-009）：`AssocIndex` 负责
find/insert/remove 键槽代数；本文件负责树链接 / 旋转 / 染色几何。 -/

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

/-- 槽下标：1-based 地址 → `Vector` 下标。 -/
@[inline] def slotIdx (a : UInt64) : Nat :=
  (a.toNat - 1) % 4

/-- 已进入 bump 区的地址（含自由链表节点）。 -/
def allocated (s : State) (a : UInt64) : Prop :=
  1 ≤ a ∧ a < s.bumpIndex

/-- 一步父子边（孩子非哨兵）。 -/
def isChild (s : State) (parent child : UInt64) : Prop :=
  child ≠ sentinel ∧
  (s.nodes[slotIdx parent]!.left = child ∨
    s.nodes[slotIdx parent]!.right = child)

/-- 有界可达性：root 起至多深度 3（N=4 树高上界）。 -/
def reachable (s : State) (a : UInt64) : Prop :=
  a ≠ sentinel ∧ s.root ≠ sentinel ∧ (
    a = s.root ∨
    isChild s s.root a ∨
    (∃ p1, isChild s s.root p1 ∧ isChild s p1 a) ∨
    (∃ p1 p2, isChild s s.root p1 ∧ isChild s p1 p2 ∧ isChild s p2 a))

/-- 父子互逆：可达节点的非哨兵孩子的 parent 字段回指自己。 -/
def parentInv (s : State) : Prop :=
  ∀ a, reachable s a →
    let n := s.nodes[slotIdx a]!
    (n.left ≠ sentinel → s.nodes[slotIdx n.left]!.parent = a) ∧
    (n.right ≠ sentinel → s.nodes[slotIdx n.right]!.parent = a)

/-- 局部 BST 序：可达节点左孩 key 更小、右孩 key 更大。 -/
def bstLocal (s : State) : Prop :=
  ∀ a, reachable s a →
    let n := s.nodes[slotIdx a]!
    (n.left ≠ sentinel → s.nodes[slotIdx n.left]!.key < n.key) ∧
    (n.right ≠ sentinel → n.key < s.nodes[slotIdx n.right]!.key)

/-- 根黑（空树或根 color = 0）。 -/
def rootBlack (s : State) : Prop :=
  s.root = sentinel ∨ s.nodes[slotIdx s.root]!.color = 0

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

theorem init_reachable_false (x a : UInt64) : ¬ reachable (init x) a := by
  intro h
  simp [reachable, init, sentinel] at h

theorem init_parentInv (x : UInt64) : parentInv (init x) := by
  intro a hr
  exact (init_reachable_false x a hr).elim

theorem init_bstLocal (x : UInt64) : bstLocal (init x) := by
  intro a hr
  exact (init_reachable_false x a hr).elim

theorem init_rootBlack (x : UInt64) : rootBlack (init x) := by
  simp [rootBlack, init, sentinel]

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

/-! ### sf-011：几何 `wf` 辅助引理与元数据保持

本批：结构谓词已在上方；此处收指针有界辅助引理，以及旋转的 size/bump/free
元数据守恒。`rotateLeft_wf` / `insertRoot_wf` / `removeNode_wf` 紧随补全。 -/

/-- `Vector.set` 在不同下标上读回旧值。 -/
private theorem vec_set_ne {α : Type} [Inhabited α] {n : Nat} (xs : Vector α n)
    (i j : Nat) (x : α) (hi : i < n) (hne : i ≠ j) (hj : j < n) :
    (xs.set i x hi)[j]! = xs[j]! := by
  show (xs.set i x hi)[j]?.get! = xs[j]!
  have h2 : (xs.set i x hi)[j]? = xs[j]? :=
    Vector.getElem?_set_ne (xs := xs) (x := x) hi hne
  rw [h2]
  simp [hj]

/-- 任意向量上单槽写入保持指针有界全称。 -/
private theorem ptr_bound_set (bump : UInt64) (nodes : Vector Node 4)
    (i : Nat) (n : Node) (hi : i < 4)
    (hold : ∀ a : UInt64, 1 ≤ a → a < bump →
      nodes[(a.toNat - 1) % 4]!.left ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.right ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.parent ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.color ≤ 1)
    (hl : n.left ≤ bump) (hr : n.right ≤ bump)
    (hp : n.parent ≤ bump) (hc : n.color ≤ 1) :
    ∀ a : UInt64, 1 ≤ a → a < bump →
      (nodes.set i n hi)[(a.toNat - 1) % 4]!.left ≤ bump ∧
      (nodes.set i n hi)[(a.toNat - 1) % 4]!.right ≤ bump ∧
      (nodes.set i n hi)[(a.toNat - 1) % 4]!.parent ≤ bump ∧
      (nodes.set i n hi)[(a.toNat - 1) % 4]!.color ≤ 1 := by
  intro a ha0 ha1
  have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases hia : i = (a.toNat - 1) % 4
  · subst hia
    rw [vec_set_self]
    exact ⟨hl, hr, hp, hc⟩
  · have hget := vec_set_ne nodes i ((a.toNat - 1) % 4) n hi hia hslot
    rw [hget]
    exact hold a ha0 ha1

/-- 仅改 `nodes` 时把指针全称推回 `wf`。 -/
private theorem wf_of_nodes (s : State) (nodes' : Vector Node 4) (hwf : wf s)
    (hptr : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
      nodes'[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
      nodes'[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
      nodes'[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
      nodes'[(a.toNat - 1) % 4]!.color ≤ 1) :
    wf { s with nodes := nodes' } := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, _⟩ := hwf
  exact ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩

/-- 只改某个槽的 `value` 保持 `wf`。 -/
theorem set_value_wf (s : State) (i : Nat) (v : UInt64) (hi : i < 4)
    (hwf : wf s) :
    wf { s with nodes := s.nodes.set i { s.nodes[i]! with value := v } } := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  refine ⟨hsz, hb1, hb5, hf5, hfb, ?_⟩
  intro a ha0 ha1
  have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases hia : i = (a.toNat - 1) % 4
  · subst hia
    rw [vec_set_self]
    exact hptr a ha0 ha1
  · have hget := vec_set_ne s.nodes i ((a.toNat - 1) % 4)
      { s.nodes[i]! with value := v } hi hia hslot
    rw [hget]
    exact hptr a ha0 ha1

/-- `paintNode` 在 `color ≤ 1` 时保持 `wf`。 -/
theorem paintNode_wf (s : State) (addr c : UInt64)
    (hwf : wf s) (hc : c ≤ 1) : wf (paintNode s addr c) := by
  unfold paintNode
  split
  · exact hwf
  · obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
    refine ⟨hsz, hb1, hb5, hf5, hfb, ?_⟩
    intro a ha0 ha1
    have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hi4 : (addr.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hia : (addr.toNat - 1) % 4 = (a.toNat - 1) % 4
    · have hold := hptr a ha0 ha1
      have hget : (s.nodes.set ((addr.toNat - 1) % 4)
          { s.nodes[(addr.toNat - 1) % 4]! with color := c } hi4)[(a.toNat - 1) % 4]! =
          { s.nodes[(addr.toNat - 1) % 4]! with color := c } := by
        rw [← hia, vec_set_self]
      rw [hget]
      -- left/right/parent of written node equal old slot fields (= a's old fields)
      have hsame : s.nodes[(addr.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
        rw [hia]
      rw [hsame]
      exact ⟨hold.1, hold.2.1, hold.2.2.1, hc⟩
    · have hget := vec_set_ne s.nodes ((addr.toNat - 1) % 4) ((a.toNat - 1) % 4)
        { s.nodes[(addr.toNat - 1) % 4]! with color := c } hi4 hia hslot
      rw [hget]
      exact hptr a ha0 ha1

/-- 旋转成功时 size / bumpIndex / freeHead 不变。 -/
theorem rotateLeft_meta (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateLeft s x = .ok (t, y)) :
    t.size = s.size ∧ t.bumpIndex = s.bumpIndex ∧ t.freeHead = s.freeHead := by
  have hs := rotateLeft_size s x h
  unfold rotateLeft at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rfl, rfl⟩)
    | rfl)

theorem rotateRight_meta (s : State) (x : UInt64) {t : State} {y : UInt64}
    (h : rotateRight s x = .ok (t, y)) :
    t.size = s.size ∧ t.bumpIndex = s.bumpIndex ∧ t.freeHead = s.freeHead := by
  have hs := rotateRight_size s x h
  unfold rotateRight at h
  repeat (first
    | split at h
    | simp only [] at h
    | simp at h
    | (obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rfl, rfl⟩)
    | rfl)

/-- 写入未分配槽（地址 `≥ bump` 且 `< 5`）不破坏已分配槽的指针有界。 -/
private theorem ptr_bound_set_unalloc (bump : UInt64) (nodes : Vector Node 4)
    (p : UInt64) (n : Node) (hp4 : p.toNat - 1 < 4)
    (hp0 : 1 ≤ p) (hp5 : p < 5) (hpb : bump ≤ p)
    (hold : ∀ a : UInt64, 1 ≤ a → a < bump →
      nodes[(a.toNat - 1) % 4]!.left ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.right ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.parent ≤ bump ∧
      nodes[(a.toNat - 1) % 4]!.color ≤ 1) :
    ∀ a : UInt64, 1 ≤ a → a < bump →
      (nodes.set (p.toNat - 1) n hp4)[(a.toNat - 1) % 4]!.left ≤ bump ∧
      (nodes.set (p.toNat - 1) n hp4)[(a.toNat - 1) % 4]!.right ≤ bump ∧
      (nodes.set (p.toNat - 1) n hp4)[(a.toNat - 1) % 4]!.parent ≤ bump ∧
      (nodes.set (p.toNat - 1) n hp4)[(a.toNat - 1) % 4]!.color ≤ 1 := by
  intro a ha0 ha1
  have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have ha0n : (1 : Nat) ≤ a.toNat := ha0
  have ha1n : a.toNat < bump.toNat := ha1
  have hp0n : (1 : Nat) ≤ p.toNat := hp0
  have hp5n : p.toNat < 5 := hp5
  have hpbn : bump.toNat ≤ p.toNat := hpb
  have hne : (p.toNat - 1) ≠ (a.toNat - 1) % 4 := by
    intro heq
    have habn : a.toNat < 5 := by omega
    have hab : a < 5 := habn
    have hpmod : (p.toNat - 1) % 4 = p.toNat - 1 := Nat.mod_eq_of_lt hp4
    have hslots : (a.toNat - 1) % 4 = (p.toNat - 1) % 4 := by omega
    have heqap : a = p := slot_inj ha0 hab hp0 hp5 hslots
    have : a.toNat = p.toNat := congrArg UInt64.toNat heqap
    omega
  have hget := vec_set_ne nodes (p.toNat - 1) ((a.toNat - 1) % 4) n hp4 hne hslot
  rw [hget]
  exact hold a ha0 ha1

/-! ### sf-011：旋转 / 插入 / 删除 `wf` 保持（续）

已收：结构谓词、`paintNode_wf` / `set_value_wf`、`rotateLeft_meta` / `rotateRight_meta`、
`rotateLeft_wf` / `rotateRight_wf`、`insertRoot_wf` /
`insertNode_wf_empty` / `insertNode_wf_update` / `fixInserted_wf` / `insertAt_wf` /
`insertNode_wf_insertAt`。
待补：`removeNode_wf`。 -/

/-! ### sf-011：旋转 `wf` 与插入保持 -/

/-- 左旋只把已分配节点间的指针重新接线，因此保持 `wf`。 -/
theorem rotateLeft_wf (s : State) (xAddress : UInt64) {t : State} {yRet : UInt64}
    (h : rotateLeft s xAddress = .ok (t, yRet))
    (hwf : wf s)
    (hx : 1 ≤ xAddress ∧ xAddress < s.bumpIndex)
    (hyAlloc : 1 ≤ s.nodes[(xAddress.toNat - 1) % 4]!.right ∧
      s.nodes[(xAddress.toNat - 1) % 4]!.right < s.bumpIndex)
    (hparentAlloc :
      s.nodes[(xAddress.toNat - 1) % 4]!.parent = 0 ∨
        (1 ≤ s.nodes[(xAddress.toNat - 1) % 4]!.parent ∧
          s.nodes[(xAddress.toNat - 1) % 4]!.parent < s.bumpIndex))
    (hinnerAlloc :
      let y := s.nodes[(xAddress.toNat - 1) % 4]!.right
      s.nodes[(y.toNat - 1) % 4]!.left = 0 ∨
        (1 ≤ s.nodes[(y.toNat - 1) % 4]!.left ∧
          s.nodes[(y.toNat - 1) % 4]!.left < s.bumpIndex)) :
    wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have hb5n : s.bumpIndex.toNat ≤ 5 := hb5
  have hx0n : (1 : Nat) ≤ xAddress.toNat := hx.1
  have hx1n : xAddress.toNat < s.bumpIndex.toNat := hx.2
  have hxi : xAddress.toNat - 1 < 4 := by omega
  have hximod : (xAddress.toNat - 1) % 4 = xAddress.toNat - 1 :=
    Nat.mod_eq_of_lt hxi
  rw [hximod] at hyAlloc hparentAlloc hinnerAlloc
  let xi := xAddress.toNat - 1
  let x := s.nodes[xi]!
  let yAddress := x.right
  change 1 ≤ yAddress ∧ yAddress < s.bumpIndex at hyAlloc
  change x.parent = 0 ∨ (1 ≤ x.parent ∧ x.parent < s.bumpIndex) at hparentAlloc
  have hy0n : (1 : Nat) ≤ yAddress.toNat := hyAlloc.1
  have hy1n : yAddress.toNat < s.bumpIndex.toNat := hyAlloc.2
  have hyi : yAddress.toNat - 1 < 4 := by omega
  have hymod : (yAddress.toNat - 1) % 4 = yAddress.toNat - 1 :=
    Nat.mod_eq_of_lt hyi
  change
    s.nodes[(yAddress.toNat - 1) % 4]!.left = 0 ∨
      (1 ≤ s.nodes[(yAddress.toNat - 1) % 4]!.left ∧
        s.nodes[(yAddress.toNat - 1) % 4]!.left < s.bumpIndex) at hinnerAlloc
  rw [hymod] at hinnerAlloc
  let yi := yAddress.toNat - 1
  let y := s.nodes[yi]!
  let innerAddress := y.left
  let parentAddress := x.parent
  change innerAddress = 0 ∨
    (1 ≤ innerAddress ∧ innerAddress < s.bumpIndex) at hinnerAlloc
  change parentAddress = 0 ∨
    (1 ≤ parentAddress ∧ parentAddress < s.bumpIndex) at hparentAlloc
  have hxLe : xAddress ≤ s.bumpIndex := Nat.le_of_lt hx.2
  have hyLe : yAddress ≤ s.bumpIndex := Nat.le_of_lt hyAlloc.2
  have hinnerLe : innerAddress ≤ s.bumpIndex := by
    rcases hinnerAlloc with hzero | halloc
    · rw [hzero]
      exact Nat.zero_le _
    · exact Nat.le_of_lt halloc.2
  have hparentLe : parentAddress ≤ s.bumpIndex := by
    rcases hparentAlloc with hzero | halloc
    · rw [hzero]
      exact Nat.zero_le _
    · exact Nat.le_of_lt halloc.2
  have hinnerCap : innerAddress.toNat ≤ 4 := by
    rcases hinnerAlloc with hzero | halloc
    · rw [hzero]
      decide
    · have halt : innerAddress.toNat < s.bumpIndex.toNat := halloc.2
      omega
  have hparentCap : parentAddress.toNat ≤ 4 := by
    rcases hparentAlloc with hzero | halloc
    · rw [hzero]
      decide
    · have halt : parentAddress.toNat < s.bumpIndex.toNat := halloc.2
      omega
  have hinnerAllocated : innerAddress ≠ 0 →
      1 ≤ innerAddress ∧ innerAddress < s.bumpIndex := by
    intro hne
    rcases hinnerAlloc with hzero | halloc
    · exact (hne hzero).elim
    · exact halloc
  have hparentAllocated : parentAddress ≠ 0 →
      1 ≤ parentAddress ∧ parentAddress < s.bumpIndex := by
    intro hne
    rcases hparentAlloc with hzero | halloc
    · exact (hne hzero).elim
    · exact halloc
  have hxptr := hptr xAddress hx.1 hx.2
  rw [hximod] at hxptr
  change x.left ≤ s.bumpIndex ∧ x.right ≤ s.bumpIndex ∧
    x.parent ≤ s.bumpIndex ∧ x.color ≤ 1 at hxptr
  have hyptr := hptr yAddress hyAlloc.1 hyAlloc.2
  rw [hymod] at hyptr
  change y.left ≤ s.bumpIndex ∧ y.right ≤ s.bumpIndex ∧
    y.parent ≤ s.bumpIndex ∧ y.color ≤ 1 at hyptr
  let nodes1 := s.nodes.set xi { x with right := innerAddress, parent := yAddress }
  have hn1 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
      nodes1[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.color ≤ 1 := by
    exact ptr_bound_set s.bumpIndex s.nodes xi
      { x with right := innerAddress, parent := yAddress } hxi hptr
      hxptr.1 hinnerLe hyLe hxptr.2.2.2
  have hxne : xAddress ≠ 0 := by
    intro hzero
    have hnat : xAddress.toNat ≠ 0 := by omega
    apply hnat
    rw [hzero]
    rfl
  have hyne : yAddress ≠ 0 := by
    intro hzero
    have hnat : yAddress.toNat ≠ 0 := by omega
    apply hnat
    rw [hzero]
    rfl
  have hinner4 : ¬(4 : UInt64) < innerAddress := by
    show ¬(4 : Nat) < innerAddress.toNat
    omega
  have hparent4 : ¬(4 : UInt64) < parentAddress := by
    show ¬(4 : Nat) < parentAddress.toNat
    omega
  simp (config := { zetaDelta := true }) only [rotateLeft, hxne, hxi, xi, x, yAddress,
    hyne, hyi, yi, y, innerAddress, parentAddress, hinner4, hparent4] at h
  by_cases hinner0 : innerAddress = 0
  · simp (config := { zetaDelta := true }) only [hinner0, if_pos] at h
    let nodes0 := s.nodes.set xi { x with right := 0, parent := yAddress }
    have hn0 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
        nodes0[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.color ≤ 1 := by
      simpa (config := { zetaDelta := true }) only [hinner0] using hn1
    by_cases hparent0 : parentAddress = 0
    · simp (config := { zetaDelta := true }) only
        [hparent0, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hy0 := hn0 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy0
      change nodes0[yi]!.left ≤ s.bumpIndex ∧
        nodes0[yi]!.right ≤ s.bumpIndex ∧
        nodes0[yi]!.parent ≤ s.bumpIndex ∧ nodes0[yi]!.color ≤ 1 at hy0
      have hfinal := ptr_bound_set s.bumpIndex nodes0 yi
        { nodes0[yi]! with left := xAddress, parent := 0 } hyi hn0
        hxLe hy0.2.1 (Nat.zero_le _) hy0.2.2.2
      exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
    · simp (config := { zetaDelta := true }) only [hparent0, if_neg] at h
      let parentIndex := (parentAddress.toNat - 1) % 4
      have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
      have hpalloc := hparentAllocated hparent0
      have hp0 := hn0 parentAddress hpalloc.1 hpalloc.2
      change nodes0[parentIndex]!.left ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.right ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.parent ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.color ≤ 1 at hp0
      have hy0 := hn0 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy0
      change nodes0[yi]!.left ≤ s.bumpIndex ∧
        nodes0[yi]!.right ≤ s.bumpIndex ∧
        nodes0[yi]!.parent ≤ s.bumpIndex ∧ nodes0[yi]!.color ≤ 1 at hy0
      by_cases hleft : nodes0[parentIndex]!.left = xAddress
      · simp (config := { zetaDelta := true }) only
          [hleft, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes0.set parentIndex { nodes0[parentIndex]! with left := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes0 parentIndex
            { nodes0[parentIndex]! with left := yAddress } hpi hn0
            hyLe hp0.2.1 hp0.2.2.1 hp0.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes0[yi]! with left := xAddress, parent := parentAddress } hyi hnP
          hxLe hy0.2.1 hparentLe hy0.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
      · simp (config := { zetaDelta := true }) only
          [hleft, if_neg, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes0.set parentIndex { nodes0[parentIndex]! with right := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes0 parentIndex
            { nodes0[parentIndex]! with right := yAddress } hpi hn0
            hp0.1 hyLe hp0.2.2.1 hp0.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes0[yi]! with left := xAddress, parent := parentAddress } hyi hnP
          hxLe hy0.2.1 hparentLe hy0.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
  · simp (config := { zetaDelta := true }) only [hinner0, if_neg] at h
    have hialloc := hinnerAllocated hinner0
    let innerIndex := (innerAddress.toNat - 1) % 4
    have hii : innerIndex < 4 := Nat.mod_lt _ (by decide)
    have hi1 := hn1 innerAddress hialloc.1 hialloc.2
    change nodes1[innerIndex]!.left ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.right ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.parent ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.color ≤ 1 at hi1
    let nodes2 :=
      nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    have hn2 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
        nodes2[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.color ≤ 1 := by
      exact ptr_bound_set s.bumpIndex nodes1 innerIndex
        { nodes1[innerIndex]! with parent := xAddress } hii hn1
        hi1.1 hi1.2.1 hxLe hi1.2.2.2
    by_cases hparent0 : parentAddress = 0
    · simp (config := { zetaDelta := true }) only
        [hparent0, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hy2 := hn2 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy2
      change nodes2[yi]!.left ≤ s.bumpIndex ∧
        nodes2[yi]!.right ≤ s.bumpIndex ∧
        nodes2[yi]!.parent ≤ s.bumpIndex ∧ nodes2[yi]!.color ≤ 1 at hy2
      have hfinal := ptr_bound_set s.bumpIndex nodes2 yi
        { nodes2[yi]! with left := xAddress, parent := 0 } hyi hn2
        hxLe hy2.2.1 (Nat.zero_le _) hy2.2.2.2
      exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
    · simp (config := { zetaDelta := true }) only [hparent0, if_neg] at h
      let parentIndex := (parentAddress.toNat - 1) % 4
      have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
      have hpalloc := hparentAllocated hparent0
      have hp2 := hn2 parentAddress hpalloc.1 hpalloc.2
      change nodes2[parentIndex]!.left ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.right ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.parent ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.color ≤ 1 at hp2
      have hy2 := hn2 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy2
      change nodes2[yi]!.left ≤ s.bumpIndex ∧
        nodes2[yi]!.right ≤ s.bumpIndex ∧
        nodes2[yi]!.parent ≤ s.bumpIndex ∧ nodes2[yi]!.color ≤ 1 at hy2
      by_cases hleft : nodes2[parentIndex]!.left = xAddress
      · simp (config := { zetaDelta := true }) only
          [hleft, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes2 parentIndex
            { nodes2[parentIndex]! with left := yAddress } hpi hn2
            hyLe hp2.2.1 hp2.2.2.1 hp2.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes2[yi]! with left := xAddress, parent := parentAddress } hyi hnP
          hxLe hy2.2.1 hparentLe hy2.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
      · simp (config := { zetaDelta := true }) only
          [hleft, if_neg, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes2 parentIndex
            { nodes2[parentIndex]! with right := yAddress } hpi hn2
            hp2.1 hyLe hp2.2.2.1 hp2.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes2[yi]! with left := xAddress, parent := parentAddress } hyi hnP
          hxLe hy2.2.1 hparentLe hy2.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩

/-- 右旋是左旋的镜像：轴的左孩与其右侧内孩须已分配或为哨兵。 -/
theorem rotateRight_wf (s : State) (xAddress : UInt64) {t : State} {yRet : UInt64}
    (h : rotateRight s xAddress = .ok (t, yRet))
    (hwf : wf s)
    (hx : 1 ≤ xAddress ∧ xAddress < s.bumpIndex)
    (hyAlloc : 1 ≤ s.nodes[(xAddress.toNat - 1) % 4]!.left ∧
      s.nodes[(xAddress.toNat - 1) % 4]!.left < s.bumpIndex)
    (hparentAlloc :
      s.nodes[(xAddress.toNat - 1) % 4]!.parent = 0 ∨
        (1 ≤ s.nodes[(xAddress.toNat - 1) % 4]!.parent ∧
          s.nodes[(xAddress.toNat - 1) % 4]!.parent < s.bumpIndex))
    (hinnerAlloc :
      let y := s.nodes[(xAddress.toNat - 1) % 4]!.left
      s.nodes[(y.toNat - 1) % 4]!.right = 0 ∨
        (1 ≤ s.nodes[(y.toNat - 1) % 4]!.right ∧
          s.nodes[(y.toNat - 1) % 4]!.right < s.bumpIndex)) :
    wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have hb5n : s.bumpIndex.toNat ≤ 5 := hb5
  have hx0n : (1 : Nat) ≤ xAddress.toNat := hx.1
  have hx1n : xAddress.toNat < s.bumpIndex.toNat := hx.2
  have hxi : xAddress.toNat - 1 < 4 := by omega
  have hximod : (xAddress.toNat - 1) % 4 = xAddress.toNat - 1 :=
    Nat.mod_eq_of_lt hxi
  rw [hximod] at hyAlloc hparentAlloc hinnerAlloc
  let xi := xAddress.toNat - 1
  let x := s.nodes[xi]!
  let yAddress := x.left
  change 1 ≤ yAddress ∧ yAddress < s.bumpIndex at hyAlloc
  change x.parent = 0 ∨ (1 ≤ x.parent ∧ x.parent < s.bumpIndex) at hparentAlloc
  have hy0n : (1 : Nat) ≤ yAddress.toNat := hyAlloc.1
  have hy1n : yAddress.toNat < s.bumpIndex.toNat := hyAlloc.2
  have hyi : yAddress.toNat - 1 < 4 := by omega
  have hymod : (yAddress.toNat - 1) % 4 = yAddress.toNat - 1 :=
    Nat.mod_eq_of_lt hyi
  change
    s.nodes[(yAddress.toNat - 1) % 4]!.right = 0 ∨
      (1 ≤ s.nodes[(yAddress.toNat - 1) % 4]!.right ∧
        s.nodes[(yAddress.toNat - 1) % 4]!.right < s.bumpIndex) at hinnerAlloc
  rw [hymod] at hinnerAlloc
  let yi := yAddress.toNat - 1
  let y := s.nodes[yi]!
  let innerAddress := y.right
  let parentAddress := x.parent
  change innerAddress = 0 ∨
    (1 ≤ innerAddress ∧ innerAddress < s.bumpIndex) at hinnerAlloc
  change parentAddress = 0 ∨
    (1 ≤ parentAddress ∧ parentAddress < s.bumpIndex) at hparentAlloc
  have hxLe : xAddress ≤ s.bumpIndex := Nat.le_of_lt hx.2
  have hyLe : yAddress ≤ s.bumpIndex := Nat.le_of_lt hyAlloc.2
  have hinnerLe : innerAddress ≤ s.bumpIndex := by
    rcases hinnerAlloc with hzero | halloc
    · rw [hzero]
      exact Nat.zero_le _
    · exact Nat.le_of_lt halloc.2
  have hparentLe : parentAddress ≤ s.bumpIndex := by
    rcases hparentAlloc with hzero | halloc
    · rw [hzero]
      exact Nat.zero_le _
    · exact Nat.le_of_lt halloc.2
  have hinnerCap : innerAddress.toNat ≤ 4 := by
    rcases hinnerAlloc with hzero | halloc
    · rw [hzero]
      decide
    · have halt : innerAddress.toNat < s.bumpIndex.toNat := halloc.2
      omega
  have hparentCap : parentAddress.toNat ≤ 4 := by
    rcases hparentAlloc with hzero | halloc
    · rw [hzero]
      decide
    · have halt : parentAddress.toNat < s.bumpIndex.toNat := halloc.2
      omega
  have hinnerAllocated : innerAddress ≠ 0 →
      1 ≤ innerAddress ∧ innerAddress < s.bumpIndex := by
    intro hne
    rcases hinnerAlloc with hzero | halloc
    · exact (hne hzero).elim
    · exact halloc
  have hparentAllocated : parentAddress ≠ 0 →
      1 ≤ parentAddress ∧ parentAddress < s.bumpIndex := by
    intro hne
    rcases hparentAlloc with hzero | halloc
    · exact (hne hzero).elim
    · exact halloc
  have hxptr := hptr xAddress hx.1 hx.2
  rw [hximod] at hxptr
  change x.left ≤ s.bumpIndex ∧ x.right ≤ s.bumpIndex ∧
    x.parent ≤ s.bumpIndex ∧ x.color ≤ 1 at hxptr
  have hyptr := hptr yAddress hyAlloc.1 hyAlloc.2
  rw [hymod] at hyptr
  change y.left ≤ s.bumpIndex ∧ y.right ≤ s.bumpIndex ∧
    y.parent ≤ s.bumpIndex ∧ y.color ≤ 1 at hyptr
  let nodes1 := s.nodes.set xi { x with left := innerAddress, parent := yAddress }
  have hn1 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
      nodes1[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
      nodes1[(a.toNat - 1) % 4]!.color ≤ 1 := by
    exact ptr_bound_set s.bumpIndex s.nodes xi
      { x with left := innerAddress, parent := yAddress } hxi hptr
      hinnerLe hxptr.2.1 hyLe hxptr.2.2.2
  have hxne : xAddress ≠ 0 := by
    intro hzero
    have hnat : xAddress.toNat ≠ 0 := by omega
    apply hnat
    rw [hzero]
    rfl
  have hyne : yAddress ≠ 0 := by
    intro hzero
    have hnat : yAddress.toNat ≠ 0 := by omega
    apply hnat
    rw [hzero]
    rfl
  have hinner4 : ¬(4 : UInt64) < innerAddress := by
    show ¬(4 : Nat) < innerAddress.toNat
    omega
  have hparent4 : ¬(4 : UInt64) < parentAddress := by
    show ¬(4 : Nat) < parentAddress.toNat
    omega
  simp (config := { zetaDelta := true }) only [rotateRight, hxne, hxi, xi, x, yAddress,
    hyne, hyi, yi, y, innerAddress, parentAddress, hinner4, hparent4] at h
  by_cases hinner0 : innerAddress = 0
  · simp (config := { zetaDelta := true }) only [hinner0, if_pos] at h
    let nodes0 := s.nodes.set xi { x with left := 0, parent := yAddress }
    have hn0 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
        nodes0[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
        nodes0[(a.toNat - 1) % 4]!.color ≤ 1 := by
      simpa (config := { zetaDelta := true }) only [hinner0] using hn1
    by_cases hparent0 : parentAddress = 0
    · simp (config := { zetaDelta := true }) only
        [hparent0, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hy0 := hn0 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy0
      change nodes0[yi]!.left ≤ s.bumpIndex ∧
        nodes0[yi]!.right ≤ s.bumpIndex ∧
        nodes0[yi]!.parent ≤ s.bumpIndex ∧ nodes0[yi]!.color ≤ 1 at hy0
      have hfinal := ptr_bound_set s.bumpIndex nodes0 yi
        { nodes0[yi]! with right := xAddress, parent := 0 } hyi hn0
        hy0.1 hxLe (Nat.zero_le _) hy0.2.2.2
      exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
    · simp (config := { zetaDelta := true }) only [hparent0, if_neg] at h
      let parentIndex := (parentAddress.toNat - 1) % 4
      have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
      have hpalloc := hparentAllocated hparent0
      have hp0 := hn0 parentAddress hpalloc.1 hpalloc.2
      change nodes0[parentIndex]!.left ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.right ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.parent ≤ s.bumpIndex ∧
        nodes0[parentIndex]!.color ≤ 1 at hp0
      have hy0 := hn0 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy0
      change nodes0[yi]!.left ≤ s.bumpIndex ∧
        nodes0[yi]!.right ≤ s.bumpIndex ∧
        nodes0[yi]!.parent ≤ s.bumpIndex ∧ nodes0[yi]!.color ≤ 1 at hy0
      by_cases hleft : nodes0[parentIndex]!.left = xAddress
      · simp (config := { zetaDelta := true }) only
          [hleft, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes0.set parentIndex { nodes0[parentIndex]! with left := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes0 parentIndex
            { nodes0[parentIndex]! with left := yAddress } hpi hn0
            hyLe hp0.2.1 hp0.2.2.1 hp0.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes0[yi]! with right := xAddress, parent := parentAddress } hyi hnP
          hy0.1 hxLe hparentLe hy0.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
      · simp (config := { zetaDelta := true }) only
          [hleft, if_neg, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes0.set parentIndex { nodes0[parentIndex]! with right := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes0 parentIndex
            { nodes0[parentIndex]! with right := yAddress } hpi hn0
            hp0.1 hyLe hp0.2.2.1 hp0.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes0[yi]! with right := xAddress, parent := parentAddress } hyi hnP
          hy0.1 hxLe hparentLe hy0.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
  · simp (config := { zetaDelta := true }) only [hinner0, if_neg] at h
    have hialloc := hinnerAllocated hinner0
    let innerIndex := (innerAddress.toNat - 1) % 4
    have hii : innerIndex < 4 := Nat.mod_lt _ (by decide)
    have hi1 := hn1 innerAddress hialloc.1 hialloc.2
    change nodes1[innerIndex]!.left ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.right ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.parent ≤ s.bumpIndex ∧
      nodes1[innerIndex]!.color ≤ 1 at hi1
    let nodes2 :=
      nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    have hn2 : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
        nodes2[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
        nodes2[(a.toNat - 1) % 4]!.color ≤ 1 := by
      exact ptr_bound_set s.bumpIndex nodes1 innerIndex
        { nodes1[innerIndex]! with parent := xAddress } hii hn1
        hi1.1 hi1.2.1 hxLe hi1.2.2.2
    by_cases hparent0 : parentAddress = 0
    · simp (config := { zetaDelta := true }) only
        [hparent0, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hy2 := hn2 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy2
      change nodes2[yi]!.left ≤ s.bumpIndex ∧
        nodes2[yi]!.right ≤ s.bumpIndex ∧
        nodes2[yi]!.parent ≤ s.bumpIndex ∧ nodes2[yi]!.color ≤ 1 at hy2
      have hfinal := ptr_bound_set s.bumpIndex nodes2 yi
        { nodes2[yi]! with right := xAddress, parent := 0 } hyi hn2
        hy2.1 hxLe (Nat.zero_le _) hy2.2.2.2
      exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
    · simp (config := { zetaDelta := true }) only [hparent0, if_neg] at h
      let parentIndex := (parentAddress.toNat - 1) % 4
      have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
      have hpalloc := hparentAllocated hparent0
      have hp2 := hn2 parentAddress hpalloc.1 hpalloc.2
      change nodes2[parentIndex]!.left ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.right ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.parent ≤ s.bumpIndex ∧
        nodes2[parentIndex]!.color ≤ 1 at hp2
      have hy2 := hn2 yAddress hyAlloc.1 hyAlloc.2
      rw [hymod] at hy2
      change nodes2[yi]!.left ≤ s.bumpIndex ∧
        nodes2[yi]!.right ≤ s.bumpIndex ∧
        nodes2[yi]!.parent ≤ s.bumpIndex ∧ nodes2[yi]!.color ≤ 1 at hy2
      by_cases hleft : nodes2[parentIndex]!.left = xAddress
      · simp (config := { zetaDelta := true }) only
          [hleft, if_pos, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes2 parentIndex
            { nodes2[parentIndex]! with left := yAddress } hpi hn2
            hyLe hp2.2.1 hp2.2.2.1 hp2.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes2[yi]! with right := xAddress, parent := parentAddress } hyi hnP
          hy2.1 hxLe hparentLe hy2.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
      · simp (config := { zetaDelta := true }) only
          [hleft, if_neg, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        let nodesP :=
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
        have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
            nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
            nodesP[(a.toNat - 1) % 4]!.color ≤ 1 := by
          exact ptr_bound_set s.bumpIndex nodes2 parentIndex
            { nodes2[parentIndex]! with right := yAddress } hpi hn2
            hp2.1 hyLe hp2.2.2.1 hp2.2.2.2
        have hfinal := ptr_bound_set s.bumpIndex nodesP yi
          { nodes2[yi]! with right := xAddress, parent := parentAddress } hyi hnP
          hy2.1 hxLe hparentLe hy2.2.2.2
        exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩

/-- `wf` 只给出 `≤ bumpIndex`；fixup 还需要非哨兵树边严格落在已分配区。 -/
def linksAllocated (s : State) : Prop :=
  ∀ a, allocated s a →
    let n := s.nodes[slotIdx a]!
    (n.left = 0 ∨ allocated s n.left) ∧
    (n.right = 0 ∨ allocated s n.right) ∧
    (n.parent = 0 ∨ allocated s n.parent)

private theorem allocated_mono {s t : State} {a : UInt64}
    (ha : allocated s a) (hbump : s.bumpIndex ≤ t.bumpIndex) : allocated t a := by
  refine ⟨ha.1, ?_⟩
  show a.toNat < t.bumpIndex.toNat
  have ha' : a.toNat < s.bumpIndex.toNat := ha.2
  have hbump' : s.bumpIndex.toNat ≤ t.bumpIndex.toNat := hbump
  omega

/-- `fixInserted` 不改 allocator 元数据；颜色翻转和 N=4 紧凑重接线只写入
哨兵或已分配地址，因此保持 `wf`。 -/
private theorem fixInserted_wf (before s : State)
    (nodeAddress parentAddress direction : UInt64) {t : State} {a : UInt64}
    (h : fixInserted before s nodeAddress parentAddress direction = .ok (t, a))
    (hwf : wf s)
    (hnode : allocated s nodeAddress)
    (hparentBefore : allocated before parentAddress)
    (hbump : before.bumpIndex ≤ s.bumpIndex)
    (hlinks : linksAllocated before) : wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  let parentIndex := (parentAddress.toNat - 1) % 4
  let grandAddress := before.nodes[parentIndex]!.parent
  let grandIndex := (grandAddress.toNat - 1) % 4
  have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
  have hgi : grandIndex < 4 := Nat.mod_lt _ (by decide)
  have hparent := allocated_mono hparentBefore hbump
  have hparentLe : parentAddress ≤ s.bumpIndex := Nat.le_of_lt hparent.2
  have hnodeLe : nodeAddress ≤ s.bumpIndex := Nat.le_of_lt hnode.2
  have hparentPtr := hptr parentAddress hparent.1 hparent.2
  change s.nodes[parentIndex]!.left ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.right ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.parent ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.color ≤ 1 at hparentPtr
  have hparentLinks := hlinks parentAddress hparentBefore
  change
    (before.nodes[parentIndex]!.left = 0 ∨
      allocated before before.nodes[parentIndex]!.left) ∧
    (before.nodes[parentIndex]!.right = 0 ∨
      allocated before before.nodes[parentIndex]!.right) ∧
    (grandAddress = 0 ∨ allocated before grandAddress) at hparentLinks
  unfold fixInserted at h
  dsimp only at h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfinal := ptr_bound_set s.bumpIndex s.nodes parentIndex
        { s.nodes[parentIndex]! with color := 0 } hpi hptr
        hparentPtr.1 hparentPtr.2.1 hparentPtr.2.2.1
        (show (0 : UInt64) ≤ 1 by decide)
      exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
    · rename_i hgrand0
      change grandAddress ≠ 0 at hgrand0
      have hgrandBefore : allocated before grandAddress := by
        rcases hparentLinks.2.2 with hzero | halloc
        · exact (hgrand0 hzero).elim
        · exact halloc
      have hgrand := allocated_mono hgrandBefore hbump
      have hgrandLe : grandAddress ≤ s.bumpIndex := Nat.le_of_lt hgrand.2
      have hgrandPtr := hptr grandAddress hgrand.1 hgrand.2
      change s.nodes[grandIndex]!.left ≤ s.bumpIndex ∧
        s.nodes[grandIndex]!.right ≤ s.bumpIndex ∧
        s.nodes[grandIndex]!.parent ≤ s.bumpIndex ∧
        s.nodes[grandIndex]!.color ≤ 1 at hgrandPtr
      have hgrandLinks := hlinks grandAddress hgrandBefore
      change
        (before.nodes[grandIndex]!.left = 0 ∨
          allocated before before.nodes[grandIndex]!.left) ∧
        (before.nodes[grandIndex]!.right = 0 ∨
          allocated before before.nodes[grandIndex]!.right) ∧
        (before.nodes[grandIndex]!.parent = 0 ∨
          allocated before before.nodes[grandIndex]!.parent) at hgrandLinks
      split at h
      · let uncleAddress := before.nodes[grandIndex]!.right
        let uncleIndex := (uncleAddress.toNat - 1) % 4
        have hui : uncleIndex < 4 := Nat.mod_lt _ (by decide)
        by_cases huncleRed :
            (if uncleAddress = 0 then 0 else before.nodes[uncleIndex]!.color) = 1
        · rw [if_pos huncleRed] at h
          have huncle0 : uncleAddress ≠ 0 := by
            intro hzero
            have h01 : (0 : UInt64) ≠ 1 := by decide
            apply h01
            simpa only [hzero, if_pos] using huncleRed
          have huncleBefore : allocated before uncleAddress := by
            rcases hgrandLinks.2.1 with hzero | halloc
            · exact (huncle0 hzero).elim
            · exact halloc
          have huncle := allocated_mono huncleBefore hbump
          have hunclePtr := hptr uncleAddress huncle.1 huncle.2
          change s.nodes[uncleIndex]!.left ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.right ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.parent ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.color ≤ 1 at hunclePtr
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          let nodesP :=
            s.nodes.set parentIndex { s.nodes[parentIndex]! with color := 0 }
          have hnP : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
              nodesP[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.color ≤ 1 :=
            ptr_bound_set s.bumpIndex s.nodes parentIndex
              { s.nodes[parentIndex]! with color := 0 } hpi hptr
              hparentPtr.1 hparentPtr.2.1 hparentPtr.2.2.1
              (show (0 : UInt64) ≤ 1 by decide)
          let nodesU :=
            nodesP.set uncleIndex { s.nodes[uncleIndex]! with color := 0 }
          have hnU : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
              nodesU[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.color ≤ 1 :=
            ptr_bound_set s.bumpIndex nodesP uncleIndex
              { s.nodes[uncleIndex]! with color := 0 } hui hnP
              hunclePtr.1 hunclePtr.2.1 hunclePtr.2.2.1
              (show (0 : UInt64) ≤ 1 by decide)
          have hfinal := ptr_bound_set s.bumpIndex nodesU grandIndex
            { s.nodes[grandIndex]! with color := 0 } hgi hnU
            hgrandPtr.1 hgrandPtr.2.1 hgrandPtr.2.2.1
            (show (0 : UInt64) ≤ 1 by decide)
          exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
        · rw [if_neg huncleRed] at h
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            let nodesP :=
              s.nodes.set parentIndex
                { s.nodes[parentIndex]! with
                  right := 0, parent := nodeAddress, color := 1 }
            have hnP : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesP[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex s.nodes parentIndex
                { s.nodes[parentIndex]! with
                  right := 0, parent := nodeAddress, color := 1 } hpi hptr
                hparentPtr.1 (Nat.zero_le _) hnodeLe
                (show (1 : UInt64) ≤ 1 by decide)
            let nodesG :=
              nodesP.set grandIndex
                { s.nodes[grandIndex]! with
                  left := 0, parent := nodeAddress, color := 1 }
            have hnG : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesG[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex nodesP grandIndex
                { s.nodes[grandIndex]! with
                  left := 0, parent := nodeAddress, color := 1 } hgi hnP
                (Nat.zero_le _) hgrandPtr.2.1 hnodeLe
                (show (1 : UInt64) ≤ 1 by decide)
            let nodeIndex := (nodeAddress.toNat - 1) % 4
            have hni : nodeIndex < 4 := Nat.mod_lt _ (by decide)
            have hfinal := ptr_bound_set s.bumpIndex nodesG nodeIndex
              { s.nodes[nodeIndex]! with
                left := parentAddress, right := grandAddress, parent := 0, color := 0 }
              hni hnG hparentLe hgrandLe (Nat.zero_le _)
              (show (0 : UInt64) ≤ 1 by decide)
            exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            let nodesG :=
              s.nodes.set grandIndex
                { s.nodes[grandIndex]! with
                  left := 0, parent := parentAddress, color := 1 }
            have hnG : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesG[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex s.nodes grandIndex
                { s.nodes[grandIndex]! with
                  left := 0, parent := parentAddress, color := 1 } hgi hptr
                (Nat.zero_le _) hgrandPtr.2.1 hparentLe
                (show (1 : UInt64) ≤ 1 by decide)
            have hfinal := ptr_bound_set s.bumpIndex nodesG parentIndex
              { s.nodes[parentIndex]! with
                right := grandAddress, parent := 0, color := 0 } hpi hnG
              hparentPtr.1 hgrandLe (Nat.zero_le _)
              (show (0 : UInt64) ≤ 1 by decide)
            exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
      · let uncleAddress := before.nodes[grandIndex]!.left
        let uncleIndex := (uncleAddress.toNat - 1) % 4
        have hui : uncleIndex < 4 := Nat.mod_lt _ (by decide)
        by_cases huncleRed :
            (if uncleAddress = 0 then 0 else before.nodes[uncleIndex]!.color) = 1
        · rw [if_pos huncleRed] at h
          have huncle0 : uncleAddress ≠ 0 := by
            intro hzero
            have h01 : (0 : UInt64) ≠ 1 := by decide
            apply h01
            simpa only [hzero, if_pos] using huncleRed
          have huncleBefore : allocated before uncleAddress := by
            rcases hgrandLinks.1 with hzero | halloc
            · exact (huncle0 hzero).elim
            · exact halloc
          have huncle := allocated_mono huncleBefore hbump
          have hunclePtr := hptr uncleAddress huncle.1 huncle.2
          change s.nodes[uncleIndex]!.left ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.right ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.parent ≤ s.bumpIndex ∧
            s.nodes[uncleIndex]!.color ≤ 1 at hunclePtr
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          let nodesP :=
            s.nodes.set parentIndex { s.nodes[parentIndex]! with color := 0 }
          have hnP : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
              nodesP[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
              nodesP[(x.toNat - 1) % 4]!.color ≤ 1 :=
            ptr_bound_set s.bumpIndex s.nodes parentIndex
              { s.nodes[parentIndex]! with color := 0 } hpi hptr
              hparentPtr.1 hparentPtr.2.1 hparentPtr.2.2.1
              (show (0 : UInt64) ≤ 1 by decide)
          let nodesU :=
            nodesP.set uncleIndex { s.nodes[uncleIndex]! with color := 0 }
          have hnU : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
              nodesU[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
              nodesU[(x.toNat - 1) % 4]!.color ≤ 1 :=
            ptr_bound_set s.bumpIndex nodesP uncleIndex
              { s.nodes[uncleIndex]! with color := 0 } hui hnP
              hunclePtr.1 hunclePtr.2.1 hunclePtr.2.2.1
              (show (0 : UInt64) ≤ 1 by decide)
          have hfinal := ptr_bound_set s.bumpIndex nodesU grandIndex
            { s.nodes[grandIndex]! with color := 0 } hgi hnU
            hgrandPtr.1 hgrandPtr.2.1 hgrandPtr.2.2.1
            (show (0 : UInt64) ≤ 1 by decide)
          exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
        · rw [if_neg huncleRed] at h
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            let nodesP :=
              s.nodes.set parentIndex
                { s.nodes[parentIndex]! with
                  left := 0, parent := nodeAddress, color := 1 }
            have hnP : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesP[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesP[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex s.nodes parentIndex
                { s.nodes[parentIndex]! with
                  left := 0, parent := nodeAddress, color := 1 } hpi hptr
                (Nat.zero_le _) hparentPtr.2.1 hnodeLe
                (show (1 : UInt64) ≤ 1 by decide)
            let nodesG :=
              nodesP.set grandIndex
                { s.nodes[grandIndex]! with
                  right := 0, parent := nodeAddress, color := 1 }
            have hnG : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesG[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex nodesP grandIndex
                { s.nodes[grandIndex]! with
                  right := 0, parent := nodeAddress, color := 1 } hgi hnP
                hgrandPtr.1 (Nat.zero_le _) hnodeLe
                (show (1 : UInt64) ≤ 1 by decide)
            let nodeIndex := (nodeAddress.toNat - 1) % 4
            have hni : nodeIndex < 4 := Nat.mod_lt _ (by decide)
            have hfinal := ptr_bound_set s.bumpIndex nodesG nodeIndex
              { s.nodes[nodeIndex]! with
                left := grandAddress, right := parentAddress, parent := 0, color := 0 }
              hni hnG hgrandLe hparentLe (Nat.zero_le _)
              (show (0 : UInt64) ≤ 1 by decide)
            exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            let nodesG :=
              s.nodes.set grandIndex
                { s.nodes[grandIndex]! with
                  right := 0, parent := parentAddress, color := 1 }
            have hnG : ∀ x : UInt64, 1 ≤ x → x < s.bumpIndex →
                nodesG[(x.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
                nodesG[(x.toNat - 1) % 4]!.color ≤ 1 :=
              ptr_bound_set s.bumpIndex s.nodes grandIndex
                { s.nodes[grandIndex]! with
                  right := 0, parent := parentAddress, color := 1 } hgi hptr
                hgrandPtr.1 (Nat.zero_le _) hparentLe
                (show (1 : UInt64) ≤ 1 by decide)
            have hfinal := ptr_bound_set s.bumpIndex nodesG parentIndex
              { s.nodes[parentIndex]! with
                left := grandAddress, parent := 0, color := 0 } hpi hnG
              hgrandLe hparentPtr.2.1 (Nat.zero_le _)
              (show (0 : UInt64) ≤ 1 by decide)
            exact ⟨hsz, hb1, hb5, hf5, hfb, hfinal⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩

/-- bump 分配后先链接父节点、再覆盖新槽所得的中间状态保持 `wf`。 -/
private theorem insertAt_bump_linked_wf (s : State)
    (parentAddress direction k v : UInt64)
    (hwf : wf s) (hsize : s.size < 4) (hbump4 : s.bumpIndex < 5)
    (hparent : allocated s parentAddress) :
    wf
      { s with
        size := s.size + 1
        bumpIndex := s.bumpIndex + 1
        freeHead := s.bumpIndex + 1
        nodes :=
          (s.nodes.set ((parentAddress.toNat - 1) % 4)
            (if direction = 0 then
              { s.nodes[(parentAddress.toNat - 1) % 4]! with left := s.bumpIndex }
            else
              { s.nodes[(parentAddress.toNat - 1) % 4]! with right := s.bumpIndex })).set
            ((s.bumpIndex.toNat - 1) % 4)
            { left := 0
              right := 0
              parent := parentAddress
              color := 1
              key := k
              value := v } } := by
  obtain ⟨_, hb1, hb5, _, _, hptr⟩ := hwf
  have hsizeN : s.size.toNat < 4 := hsize
  have hb1N : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
  have hbump4N : s.bumpIndex.toNat < 5 := hbump4
  have hparent0N : (1 : Nat) ≤ parentAddress.toNat := hparent.1
  have hparentBN : parentAddress.toNat < s.bumpIndex.toNat := hparent.2
  have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
    u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
  have hbumpNew : s.bumpIndex ≤ s.bumpIndex + 1 := by
    show s.bumpIndex.toNat ≤ (s.bumpIndex + 1).toNat
    rw [hbi]
    omega
  have hleNew : ∀ {x : UInt64}, x ≤ s.bumpIndex → x ≤ s.bumpIndex + 1 := by
    intro x hx
    show x.toNat ≤ (s.bumpIndex + 1).toNat
    have hx' : x.toNat ≤ s.bumpIndex.toNat := hx
    rw [hbi]
    omega
  let parentIndex := (parentAddress.toNat - 1) % 4
  let freshIndex := (s.bumpIndex.toNat - 1) % 4
  have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
  have hfi : freshIndex < 4 := Nat.mod_lt _ (by decide)
  have hparentPtr := hptr parentAddress hparent.1 hparent.2
  change s.nodes[parentIndex]!.left ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.right ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.parent ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.color ≤ 1 at hparentPtr
  refine ⟨?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
  · show (s.size + 1).toNat ≤ 4
    rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
    omega
  · show (1 : Nat) ≤ (s.bumpIndex + 1).toNat
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
    rw [hbi] at ha1'
    have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hafresh : a = s.bumpIndex
    · subst a
      rw [vec_set_self]
      exact ⟨Nat.zero_le _, Nat.zero_le _, hleNew (Nat.le_of_lt hparent.2),
        show (1 : UInt64) ≤ 1 by decide⟩
    · have haOld : a < s.bumpIndex := by
        show a.toNat < s.bumpIndex.toNat
        have hne : a.toNat ≠ s.bumpIndex.toNat := by
          intro heq
          exact hafresh (UInt64.toNat_inj.mp heq)
        omega
      have ha5 : a < 5 := by
        show a.toNat < 5
        omega
      have hbump5 : s.bumpIndex < 5 := hbump4
      have hfreshNe : freshIndex ≠ (a.toNat - 1) % 4 := by
        intro heq
        have : s.bumpIndex = a :=
          slot_inj hb1 hbump5 ha0 ha5 heq
        exact hafresh this.symm
      rw [vec_set_ne _ freshIndex ((a.toNat - 1) % 4) _ hfi hfreshNe hslot]
      by_cases haparent : a = parentAddress
      · subst a
        rw [vec_set_self]
        by_cases hdir : direction = 0
        · simp only [hdir, if_pos]
          exact ⟨hbumpNew, hleNew hparentPtr.2.1, hleNew hparentPtr.2.2.1,
            hparentPtr.2.2.2⟩
        · simp only [hdir, if_neg]
          exact ⟨hleNew hparentPtr.1, hbumpNew, hleNew hparentPtr.2.2.1,
            hparentPtr.2.2.2⟩
      · have hparent5 : parentAddress < 5 := by
          show parentAddress.toNat < 5
          have hp' : parentAddress.toNat < s.bumpIndex.toNat := hparent.2
          omega
        have hparentNe : parentIndex ≠ (a.toNat - 1) % 4 := by
          intro heq
          have : parentAddress = a :=
            slot_inj hparent.1 hparent5 ha0 ha5 heq
          exact haparent this.symm
        rw [vec_set_ne _ parentIndex ((a.toNat - 1) % 4) _ hpi hparentNe hslot]
        obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 haOld
        exact ⟨hleNew hl, hleNew hr, hleNew hp, hc⟩

/-- free-list 分配保持 bump 不变；父链接和回收槽覆盖均只写入有界指针。 -/
private theorem insertAt_free_linked_wf (s : State)
    (parentAddress direction k v : UInt64)
    (hwf : wf s) (hsize : s.size < 4)
    (hparent : allocated s parentAddress) (hfree : allocated s s.freeHead) :
    wf
      { s with
        size := s.size + 1
        freeHead := s.nodes[(s.freeHead.toNat - 1) % 4]!.left
        nodes :=
          (s.nodes.set ((parentAddress.toNat - 1) % 4)
            (if direction = 0 then
              { s.nodes[(parentAddress.toNat - 1) % 4]! with left := s.freeHead }
            else
              { s.nodes[(parentAddress.toNat - 1) % 4]! with right := s.freeHead })).set
            ((s.freeHead.toNat - 1) % 4)
            { left := 0
              right := 0
              parent := parentAddress
              color := 1
              key := k
              value := v } } := by
  obtain ⟨_, hb1, hb5, _, _, hptr⟩ := hwf
  let parentIndex := (parentAddress.toNat - 1) % 4
  let freeIndex := (s.freeHead.toNat - 1) % 4
  have hpi : parentIndex < 4 := Nat.mod_lt _ (by decide)
  have hfi : freeIndex < 4 := Nat.mod_lt _ (by decide)
  have hparentLe : parentAddress ≤ s.bumpIndex := Nat.le_of_lt hparent.2
  have hfreeLe : s.freeHead ≤ s.bumpIndex := Nat.le_of_lt hfree.2
  have hparentPtr := hptr parentAddress hparent.1 hparent.2
  change s.nodes[parentIndex]!.left ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.right ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.parent ≤ s.bumpIndex ∧
    s.nodes[parentIndex]!.color ≤ 1 at hparentPtr
  have hfreePtr := hptr s.freeHead hfree.1 hfree.2
  change s.nodes[freeIndex]!.left ≤ s.bumpIndex ∧
    s.nodes[freeIndex]!.right ≤ s.bumpIndex ∧
    s.nodes[freeIndex]!.parent ≤ s.bumpIndex ∧
    s.nodes[freeIndex]!.color ≤ 1 at hfreePtr
  let linkedParent :=
    if direction = 0 then
      { s.nodes[parentIndex]! with left := s.freeHead }
    else
      { s.nodes[parentIndex]! with right := s.freeHead }
  have hlinkedPtr :
      linkedParent.left ≤ s.bumpIndex ∧ linkedParent.right ≤ s.bumpIndex ∧
      linkedParent.parent ≤ s.bumpIndex ∧ linkedParent.color ≤ 1 := by
    by_cases hdir : direction = 0
    · simp only [linkedParent, hdir, if_pos]
      exact ⟨hfreeLe, hparentPtr.2.1, hparentPtr.2.2.1, hparentPtr.2.2.2⟩
    · simp only [linkedParent, hdir, if_neg]
      exact ⟨hparentPtr.1, hfreeLe, hparentPtr.2.2.1, hparentPtr.2.2.2⟩
  let nodesP := s.nodes.set parentIndex linkedParent
  have hnP : ∀ a : UInt64, 1 ≤ a → a < s.bumpIndex →
      nodesP[(a.toNat - 1) % 4]!.left ≤ s.bumpIndex ∧
      nodesP[(a.toNat - 1) % 4]!.right ≤ s.bumpIndex ∧
      nodesP[(a.toNat - 1) % 4]!.parent ≤ s.bumpIndex ∧
      nodesP[(a.toNat - 1) % 4]!.color ≤ 1 :=
    ptr_bound_set s.bumpIndex s.nodes parentIndex linkedParent hpi hptr
      hlinkedPtr.1 hlinkedPtr.2.1 hlinkedPtr.2.2.1 hlinkedPtr.2.2.2
  let freshNode : Node :=
    { left := 0
      right := 0
      parent := parentAddress
      color := 1
      key := k
      value := v }
  have hfinal := ptr_bound_set s.bumpIndex nodesP freeIndex freshNode hfi hnP
    (Nat.zero_le _) (Nat.zero_le _) hparentLe (show (1 : UInt64) ≤ 1 by decide)
  refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
  · show (s.size + 1).toNat ≤ 4
    have hsizeN : s.size.toNat < 4 := hsize
    rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]
    omega
  · show s.nodes[freeIndex]!.left.toNat ≤ 5
    have : s.nodes[freeIndex]!.left.toNat ≤ s.bumpIndex.toNat := hfreePtr.1
    have hb5N : s.bumpIndex.toNat ≤ 5 := hb5
    omega
  · show s.nodes[freeIndex]!.left ≤ s.bumpIndex
    exact hfreePtr.1
  · exact hfinal

/-- `insertRoot` 成功路径保持 `wf`（对齐 `allocNode_wf` 的 bump / free-list 两臂）。 -/
private theorem insertRoot_wf (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : insertRoot s k v = .ok (t, a)) (hwf : wf s) : wf t := by
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  unfold insertRoot at h
  split at h
  · rename_i hsz4
    by_cases hfr : s.freeHead = s.bumpIndex
    · -- bump arm
      simp (config := { zeta := true }) [hfr] at h
      split at h
      · simp at h
      · rename_i hb0
        split at h
        · rename_i hb4
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hb : s.bumpIndex.toNat < 5 := hb4
          have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
            u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
          refine ⟨?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]; omega
          · show (1 : Nat) ≤ (s.bumpIndex + 1).toNat
            have hb1' : (1 : Nat) ≤ s.bumpIndex.toNat := hb1
            rw [hbi]; omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]; omega
          · show (s.bumpIndex + 1).toNat ≤ 5
            rw [hbi]; omega
          · intro a ha0 ha1
            have ha1' : a.toNat < (s.bumpIndex + 1).toNat := ha1
            rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)] at ha1'
            by_cases hab : a = s.bumpIndex
            · rw [hab, vec_set_self]
              exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.bumpIndex.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by omega
                exact hab (slot_inj ha0 ha5 hb1 hb heq)
              have hslot_lt : (a.toNat - 1) % 4 < 4 := by omega
              have hlt : a < s.bumpIndex := by
                have hne : a.toNat ≠ s.bumpIndex.toNat := by
                  intro heq; exact hab (UInt64.toNat_inj.mp heq)
                show a.toNat < s.bumpIndex.toNat; omega
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
                rw [h2]; simp [hslot_lt]
              rw [hget]
              obtain ⟨hl, hr, hp, hc⟩ := hptr a ha0 hlt
              refine ⟨?_, ?_, ?_, hc⟩
              · have hf' : (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
                show (s.nodes[(a.toNat - 1) % 4]!).left.toNat ≤ (s.bumpIndex + 1).toNat
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]; omega
              · have hf' : (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ s.bumpIndex.toNat := hr
                show (s.nodes[(a.toNat - 1) % 4]!).right.toNat ≤ (s.bumpIndex + 1).toNat
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]; omega
              · have hf' : (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ s.bumpIndex.toNat := hp
                show (s.nodes[(a.toNat - 1) % 4]!).parent.toNat ≤ (s.bumpIndex + 1).toNat
                rw [u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)]; omega
        · simp at h
    · -- free-list arm
      simp (config := { zeta := true }) [hfr] at h
      split at h
      · simp at h
      · rename_i hf0
        split at h
        · rename_i hf4
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne0 : s.freeHead ≠ 0 := hf0
          have hfh : (1 : Nat) ≤ s.freeHead.toNat := by
            have : s.freeHead.toNat ≠ 0 := by
              intro heq; exact hne0 (UInt64.toNat_inj.mp heq)
            omega
          have hle' : s.freeHead.toNat ≤ s.bumpIndex.toNat := hfb
          have hb5' : s.bumpIndex.toNat ≤ 5 := hb5
          have hfblt : s.freeHead.toNat < s.bumpIndex.toNat := by
            have hne : s.freeHead.toNat ≠ s.bumpIndex.toNat := fun heq =>
              hfr (UInt64.toNat_inj.mp heq)
            omega
          have hfh4 : s.freeHead < 5 := by
            show s.freeHead.toNat < 5; omega
          have hmod : (s.freeHead.toNat - 1) % 4 = s.freeHead.toNat - 1 := by
            have : s.freeHead.toNat - 1 < 4 := by omega
            exact Nat.mod_eq_of_lt this
          have hptr' := hptr s.freeHead hfh hfblt
          obtain ⟨hl, _, _, _⟩ := hptr'
          have hl' : (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ s.bumpIndex.toNat := hl
          refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
          · show (s.size + 1).toNat ≤ 4
            have hst : s.size.toNat < 4 := hsz4
            rw [u64_toNat_add_one (show s.size.toNat < 6 by omega)]; omega
          · -- new freeHead = old nodes[free].left
            show (s.nodes[(s.freeHead.toNat - 1) % 4]!).left.toNat ≤ 5
            have hb : s.bumpIndex.toNat ≤ 5 := hb5
            omega
          · show (s.nodes[(s.freeHead.toNat - 1) % 4]!).left ≤ s.bumpIndex
            exact hl'
          · intro a ha0 ha1
            have ha0n : (1 : Nat) ≤ a.toNat := ha0
            have ha1n : a.toNat < s.bumpIndex.toNat := ha1
            have hb5n : s.bumpIndex.toNat ≤ 5 := hb5
            have hfh_to : (1 : Nat) ≤ s.freeHead.toNat := hfh
            have hfh4n : s.freeHead.toNat < 5 := hfh4
            by_cases hab : a = s.freeHead
            · rw [hab, vec_set_self]
              exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
            · have hslot_ne : (a.toNat - 1) % 4 ≠ (s.freeHead.toNat - 1) % 4 := by
                intro heq
                have ha5 : a.toNat < 5 := by omega
                exact hab (slot_inj ha0 ha5 hfh hfh4 heq)
              have hlt : a < s.bumpIndex := ha1
              have hslot_lt : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
              have hidx : (s.freeHead.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
              have hget : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  hidx)[(a.toNat - 1) % 4]! = s.nodes[(a.toNat - 1) % 4]! := by
                show (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  hidx)[(a.toNat - 1) % 4]?.get! = _
                have h2 : (s.nodes.set ((s.freeHead.toNat - 1) % 4)
                  ({ left := 0, right := 0, parent := 0, color := 0, key := k, value := v } : Node)
                  hidx)[(a.toNat - 1) % 4]? = s.nodes[(a.toNat - 1) % 4]? := by
                  simp [Vector.getElem_set, Ne.symm hslot_ne]
                rw [h2]; simp [hslot_lt]
              rw [hget]
              obtain ⟨hl2, hr2, hp2, hc2⟩ := hptr a ha0 hlt
              exact ⟨hl2, hr2, hp2, hc2⟩
        · simp at h
  · simp at h

/-- `insertAt` 成功分配红叶、链接父节点并完成 fixup 后保持 `wf`。 -/
private theorem insertAt_wf (s : State) (parentAddress direction k v : UInt64)
    {t : State} {a : UInt64}
    (h : insertAt s parentAddress direction k v = .ok (t, a))
    (hwf : wf s) (hparent : allocated s parentAddress)
    (hlinks : linksAllocated s) : wf t := by
  have hb1 : (1 : Nat) ≤ s.bumpIndex.toNat := hwf.2.1
  have hb5 : s.bumpIndex.toNat ≤ 5 := hwf.2.2.1
  have hfb : s.freeHead.toNat ≤ s.bumpIndex.toNat := hwf.2.2.2.2.1
  unfold insertAt at h
  split at h
  · rename_i hsize
    by_cases hfresh : s.freeHead = s.bumpIndex
    · simp (config := { zeta := true }) [hfresh] at h
      split at h
      · simp at h
      · split at h
        · rename_i hbump4
          let parentIndex := (parentAddress.toNat - 1) % 4
          let linkedParent :=
            if direction = 0 then
              { s.nodes[parentIndex]! with left := s.bumpIndex }
            else
              { s.nodes[parentIndex]! with right := s.bumpIndex }
          let linked : State :=
            { s with
              size := s.size + 1
              bumpIndex := s.bumpIndex + 1
              freeHead := s.bumpIndex + 1
              nodes :=
                (s.nodes.set parentIndex linkedParent).set
                  ((s.bumpIndex.toNat - 1) % 4)
                  { left := 0
                    right := 0
                    parent := parentAddress
                    color := 1
                    key := k
                    value := v } }
          change fixInserted s linked s.bumpIndex parentAddress direction = .ok (t, a) at h
          have hlinked : wf linked := by
            exact insertAt_bump_linked_wf s parentAddress direction k v hwf hsize hbump4 hparent
          have hbi : (s.bumpIndex + 1).toNat = s.bumpIndex.toNat + 1 :=
            u64_toNat_add_one (show s.bumpIndex.toNat < 6 by omega)
          have hnode : allocated linked s.bumpIndex := by
            refine ⟨hb1, ?_⟩
            show s.bumpIndex.toNat < (s.bumpIndex + 1).toNat
            rw [hbi]
            omega
          have hbumpMono : s.bumpIndex ≤ linked.bumpIndex := by
            show s.bumpIndex.toNat ≤ (s.bumpIndex + 1).toNat
            rw [hbi]
            omega
          exact fixInserted_wf s linked s.bumpIndex parentAddress direction h
            hlinked hnode hparent hbumpMono hlinks
        · simp at h
    · simp (config := { zeta := true }) [hfresh] at h
      split at h
      · simp at h
      · rename_i hfree0
        split at h
        · rename_i hfree4
          have hfree : allocated s s.freeHead := by
            refine ⟨?_, ?_⟩
            · show (1 : Nat) ≤ s.freeHead.toNat
              have hne : s.freeHead.toNat ≠ 0 := by
                intro heq
                exact hfree0 (UInt64.toNat_inj.mp heq)
              omega
            · show s.freeHead.toNat < s.bumpIndex.toNat
              have hne : s.freeHead.toNat ≠ s.bumpIndex.toNat := by
                intro heq
                exact hfresh (UInt64.toNat_inj.mp heq)
              omega
          let parentIndex := (parentAddress.toNat - 1) % 4
          let freeIndex := (s.freeHead.toNat - 1) % 4
          let linkedParent :=
            if direction = 0 then
              { s.nodes[parentIndex]! with left := s.freeHead }
            else
              { s.nodes[parentIndex]! with right := s.freeHead }
          let linked : State :=
            { s with
              size := s.size + 1
              freeHead := s.nodes[freeIndex]!.left
              nodes :=
                (s.nodes.set parentIndex linkedParent).set freeIndex
                  { left := 0
                    right := 0
                    parent := parentAddress
                    color := 1
                    key := k
                    value := v } }
          change fixInserted s linked s.freeHead parentAddress direction = .ok (t, a) at h
          have hlinked : wf linked := by
            exact insertAt_free_linked_wf s parentAddress direction k v hwf hsize hparent hfree
          have hnode : allocated linked s.freeHead := hfree
          exact fixInserted_wf s linked s.freeHead parentAddress direction h
            hlinked hnode hparent (Nat.le_refl _) hlinks
        · simp at h
  · simp at h

/-- 非空 miss 臂已经约化为 `insertAt` 时，复用其保持定理。 -/
theorem insertNode_wf_insertAt (s : State) (k v parentAddress direction : UInt64)
    {t : State} {a : UInt64}
    (h : insertNode s k v = .ok (t, a))
    (harm : insertNode s k v = insertAt s parentAddress direction k v)
    (hwf : wf s) (hparent : allocated s parentAddress)
    (hlinks : linksAllocated s) : wf t := by
  have hi : insertAt s parentAddress direction k v = .ok (t, a) := harm ▸ h
  exact insertAt_wf s parentAddress direction k v hi hwf hparent hlinks

/-- 空树插入：`insertNode` 走 `insertRoot`，保持 `wf`。 -/
theorem insertNode_wf_empty (s : State) (k v : UInt64) {t : State} {a : UInt64}
    (h : insertNode s k v = .ok (t, a)) (hwf : wf s) (hroot : s.root = 0) : wf t := by
  unfold insertNode at h
  split at h
  · exact insertRoot_wf s k v h hwf
  · rename_i hne
    exact (hne hroot).elim

/-- 命中已有键时只改 value，保持 `wf`。 -/
theorem insertNode_wf_update (s : State) (i : Nat) (v : UInt64) (hi : i < 4)
    (hwf : wf s) :
    wf { s with nodes := s.nodes.set i { s.nodes[i]! with value := v } } :=
  set_value_wf s i v hi hwf

/-! ### sf-011：删除管线的几何保持 -/

/-- 删除 fixup 所需的严格链接边界：哨兵或 bump 区内地址。 -/
private def linkAllocated (s : State) (a : UInt64) : Prop :=
  a = 0 ∨ allocated s a

/-- 删除内部步骤同时维护基础 `wf` 与非哨兵链接已分配性。 -/
private def deleteGeom (s : State) : Prop :=
  wf s ∧ linksAllocated s

private theorem linkAllocated_le {s : State} {a : UInt64}
    (ha : linkAllocated s a) : a ≤ s.bumpIndex := by
  rcases ha with hzero | halloc
  · rw [hzero]
    exact Nat.zero_le _
  · exact Nat.le_of_lt halloc.2

private theorem allocated_of_bump_eq {s t : State} {a : UInt64}
    (ha : allocated s a) (hbump : t.bumpIndex = s.bumpIndex) : allocated t a := by
  simpa only [allocated, hbump] using ha

private theorem linkAllocated_of_bump_eq {s t : State} {a : UInt64}
    (ha : linkAllocated s a) (hbump : t.bumpIndex = s.bumpIndex) :
    linkAllocated t a := by
  simpa only [linkAllocated, allocated, hbump] using ha

private theorem transplantNode_bumpIndex (s : State) (removed replacement : UInt64) :
    (transplantNode s removed replacement).bumpIndex = s.bumpIndex := by
  unfold transplantNode
  dsimp only
  repeat (first | split | rfl)

private theorem linkLeft_bumpIndex (s : State) (parent child : UInt64) :
    (linkLeft s parent child).bumpIndex = s.bumpIndex := by
  unfold linkLeft
  dsimp only
  split <;> rfl

private theorem linkRight_bumpIndex (s : State) (parent child : UInt64) :
    (linkRight s parent child).bumpIndex = s.bumpIndex := by
  unfold linkRight
  dsimp only
  split <;> rfl

private theorem paintNode_bumpIndex (s : State) (addr color : UInt64) :
    (paintNode s addr color).bumpIndex = s.bumpIndex := by
  unfold paintNode
  split <;> rfl

private theorem rotateLeftDelete_bumpIndex (s : State) (xAddress : UInt64) :
    (rotateLeftDelete s xAddress).bumpIndex = s.bumpIndex := by
  unfold rotateLeftDelete
  dsimp only
  split <;> rfl

private theorem rotateRightDelete_bumpIndex (s : State) (xAddress : UInt64) :
    (rotateRightDelete s xAddress).bumpIndex = s.bumpIndex := by
  unfold rotateRightDelete
  dsimp only
  split <;> rfl

/-- 对任意槽写入一个几何有界节点，同时保持删除所需的两层不变量。 -/
private theorem deleteGeom_set (s : State) (i : Nat) (n : Node) (hi : i < 4)
    (hg : deleteGeom s)
    (hl : linkAllocated s n.left) (hr : linkAllocated s n.right)
    (hp : linkAllocated s n.parent) (hc : n.color ≤ 1) :
    deleteGeom { s with nodes := s.nodes.set i n } := by
  obtain ⟨hwf, hlinks⟩ := hg
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  constructor
  · exact ⟨hsz, hb1, hb5, hf5, hfb,
      ptr_bound_set s.bumpIndex s.nodes i n hi hptr
        (linkAllocated_le hl) (linkAllocated_le hr) (linkAllocated_le hp) hc⟩
  · intro a ha
    change
      let node := (s.nodes.set i n)[slotIdx a]!
      (node.left = 0 ∨ allocated { s with nodes := s.nodes.set i n } node.left) ∧
      (node.right = 0 ∨ allocated { s with nodes := s.nodes.set i n } node.right) ∧
      (node.parent = 0 ∨ allocated { s with nodes := s.nodes.set i n } node.parent)
    dsimp only
    have hslot : slotIdx a < 4 := Nat.mod_lt _ (by decide)
    by_cases hia : i = slotIdx a
    · subst hia
      rw [vec_set_self]
      simpa only [linkAllocated, allocated] using And.intro hl (And.intro hr hp)
    · rw [vec_set_ne s.nodes i (slotIdx a) n hi hia hslot]
      simpa only [allocated] using hlinks a ha

/-- 改 root 不触碰 allocator 或节点槽。 -/
private theorem deleteGeom_root (s : State) (root : UInt64)
    (hg : deleteGeom s) : deleteGeom { s with root := root } := by
  simpa only [deleteGeom, wf, linksAllocated, allocated] using hg

/-- 染色不改变任何链接，故同时保持 `wf` 与严格链接边界。 -/
private theorem paintNode_deleteGeom (s : State) (addr c : UInt64)
    (hg : deleteGeom s) (hc : c ≤ 1) : deleteGeom (paintNode s addr c) := by
  constructor
  · exact paintNode_wf s addr c hg.1 hc
  · unfold paintNode
    split
    · exact hg.2
    · intro a ha
      change
        let node :=
          (s.nodes.set ((addr.toNat - 1) % 4)
            { s.nodes[(addr.toNat - 1) % 4]! with color := c })[slotIdx a]!
        (node.left = 0 ∨ allocated s node.left) ∧
        (node.right = 0 ∨ allocated s node.right) ∧
        (node.parent = 0 ∨ allocated s node.parent)
      dsimp only
      have hslot : slotIdx a < 4 := Nat.mod_lt _ (by decide)
      have hi : (addr.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
      by_cases hia : (addr.toNat - 1) % 4 = slotIdx a
      · have hget :
            (s.nodes.set ((addr.toNat - 1) % 4)
              { s.nodes[(addr.toNat - 1) % 4]! with color := c })[slotIdx a]! =
              { s.nodes[(addr.toNat - 1) % 4]! with color := c } := by
            rw [← hia, vec_set_self]
        rw [hget]
        have hsame :
            s.nodes[(addr.toNat - 1) % 4]! = s.nodes[slotIdx a]! := by
          rw [hia]
        rw [hsame]
        exact hg.2 a ha
      · rw [vec_set_ne s.nodes ((addr.toNat - 1) % 4) (slotIdx a)
          { s.nodes[(addr.toNat - 1) % 4]! with color := c } hi hia hslot]
        exact hg.2 a ha

/-- 哨兵地址按槽读取时与地址 1 同槽；只要存在一个已分配地址，该槽也受几何约束。 -/
private theorem treeNode_deleteGeom (s : State) (addr witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (ha : linkAllocated s addr) :
    linkAllocated s (treeNode s addr).left ∧
      linkAllocated s (treeNode s addr).right ∧
      linkAllocated s (treeNode s addr).parent ∧
      (treeNode s addr).color ≤ 1 := by
  obtain ⟨hwf, hlinks⟩ := hg
  obtain ⟨_, _, _, _, _, hptr⟩ := hwf
  have hone : allocated s 1 := by
    refine ⟨by decide, ?_⟩
    have hw0 : (1 : Nat) ≤ witness.toNat := hwitness.1
    have hw1 : witness.toNat < s.bumpIndex.toNat := hwitness.2
    show (1 : Nat) < s.bumpIndex.toNat
    omega
  rcases ha with hzero | halloc
  · subst addr
    have hlink := hlinks 1 hone
    have hbound := hptr 1 hone.1 hone.2
    have hcolor : (s.nodes[0]!).color ≤ 1 := by simpa using hbound.2.2.2
    simpa [linkAllocated, treeNode, linksAllocated, slotIdx, allocated] using
      And.intro hlink.1 (And.intro hlink.2.1 (And.intro hlink.2.2 hcolor))
  · have hlink := hlinks addr halloc
    have hbound := hptr addr halloc.1 halloc.2
    simpa only [linkAllocated, treeNode, linksAllocated, slotIdx] using
      And.intro hlink.1
        (And.intro hlink.2.1 (And.intro hlink.2.2 hbound.2.2.2))

private theorem linkLeft_deleteGeom (s : State) (parent child witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hparent : allocated s parent) (hchild : linkAllocated s child) :
    deleteGeom (linkLeft s parent child) := by
  have hp := treeNode_deleteGeom s parent witness hg hwitness (Or.inr hparent)
  unfold linkLeft
  dsimp only
  split
  · exact deleteGeom_set s ((parent.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with left := child }
      (Nat.mod_lt _ (by decide)) hg hchild hp.2.1 hp.2.2.1 hp.2.2.2
  · rename_i hchild0
    have hchildAlloc : allocated s child := hchild.resolve_left hchild0
    let parentIndex := (parent.toNat - 1) % 4
    let childIndex := (child.toNat - 1) % 4
    let nodes1 :=
      s.nodes.set parentIndex { s.nodes[parentIndex]! with left := child }
    have hg1 : deleteGeom { s with nodes := nodes1 } :=
      deleteGeom_set s parentIndex { s.nodes[parentIndex]! with left := child }
        (Nat.mod_lt _ (by decide)) hg hchild hp.2.1 hp.2.2.1 hp.2.2.2
    have hc := treeNode_deleteGeom s child witness hg hwitness (Or.inr hchildAlloc)
    exact deleteGeom_set { s with nodes := nodes1 } childIndex
      { s.nodes[childIndex]! with parent := parent }
      (Nat.mod_lt _ (by decide)) hg1
      (by simpa only [linkAllocated, allocated, treeNode, childIndex] using hc.1)
      (by simpa only [linkAllocated, allocated, treeNode, childIndex] using hc.2.1)
      (by simpa only [linkAllocated, allocated] using (Or.inr hparent : linkAllocated s parent))
      (by simpa only [treeNode, childIndex] using hc.2.2.2)

private theorem linkRight_deleteGeom (s : State) (parent child witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hparent : allocated s parent) (hchild : linkAllocated s child) :
    deleteGeom (linkRight s parent child) := by
  have hp := treeNode_deleteGeom s parent witness hg hwitness (Or.inr hparent)
  unfold linkRight
  dsimp only
  split
  · exact deleteGeom_set s ((parent.toNat - 1) % 4)
      { s.nodes[(parent.toNat - 1) % 4]! with right := child }
      (Nat.mod_lt _ (by decide)) hg hp.1 hchild hp.2.2.1 hp.2.2.2
  · rename_i hchild0
    have hchildAlloc : allocated s child := hchild.resolve_left hchild0
    let parentIndex := (parent.toNat - 1) % 4
    let childIndex := (child.toNat - 1) % 4
    let nodes1 :=
      s.nodes.set parentIndex { s.nodes[parentIndex]! with right := child }
    have hg1 : deleteGeom { s with nodes := nodes1 } :=
      deleteGeom_set s parentIndex { s.nodes[parentIndex]! with right := child }
        (Nat.mod_lt _ (by decide)) hg hp.1 hchild hp.2.2.1 hp.2.2.2
    have hc := treeNode_deleteGeom s child witness hg hwitness (Or.inr hchildAlloc)
    exact deleteGeom_set { s with nodes := nodes1 } childIndex
      { s.nodes[childIndex]! with parent := parent }
      (Nat.mod_lt _ (by decide)) hg1
      (by simpa only [linkAllocated, allocated, treeNode, childIndex] using hc.1)
      (by simpa only [linkAllocated, allocated, treeNode, childIndex] using hc.2.1)
      (by simpa only [linkAllocated, allocated] using (Or.inr hparent : linkAllocated s parent))
      (by simpa only [treeNode, childIndex] using hc.2.2.2)

/-- `transplantNode` 只改父链接、root 与 replacement.parent，保持删除几何。 -/
private theorem transplantNode_deleteGeom (s : State) (removed replacement : UInt64)
    (hg : deleteGeom s) (hremoved : allocated s removed)
    (hreplacement : linkAllocated s replacement) :
    deleteGeom (transplantNode s removed replacement) := by
  let removedNode := treeNode s removed
  let parent := removedNode.parent
  have hr := treeNode_deleteGeom s removed removed hg hremoved (Or.inr hremoved)
  change linkAllocated s removedNode.left ∧
    linkAllocated s removedNode.right ∧ linkAllocated s parent ∧
    removedNode.color ≤ 1 at hr
  have hparent := hr.2.2.1
  unfold transplantNode
  dsimp only
  by_cases hparent0raw : (treeNode s removed).parent = 0
  · have hparent0 : parent = 0 := hparent0raw
    simp only [hparent0raw, if_pos]
    let parentLinked := { s with root := replacement }
    have hgP : deleteGeom parentLinked := deleteGeom_root s replacement hg
    by_cases hreplacement0 : replacement = 0
    · simpa [parentLinked, hparent0raw, hreplacement0] using hgP
    · simp only [hreplacement0, if_neg]
      have hreplacementAlloc : allocated s replacement :=
        hreplacement.resolve_left hreplacement0
      have hreplacementP : allocated parentLinked replacement := by
        simpa only [parentLinked, allocated] using hreplacementAlloc
      have hremovedP : allocated parentLinked removed := by
        simpa only [parentLinked, allocated] using hremoved
      have hn := treeNode_deleteGeom parentLinked replacement removed hgP hremovedP
        (Or.inr hreplacementP)
      simpa [parentLinked, parent, removedNode, hparent0raw, hreplacement0] using
        deleteGeom_set parentLinked ((replacement.toNat - 1) % 4)
          { parentLinked.nodes[(replacement.toNat - 1) % 4]! with parent := parent }
          (Nat.mod_lt _ (by decide)) hgP hn.1 hn.2.1
          (by simpa only [parentLinked, linkAllocated, allocated] using hparent)
          hn.2.2.2
  · have hparent0 : parent ≠ 0 := hparent0raw
    simp only [hparent0raw, if_neg]
    have hparentAlloc : allocated s parent := hparent.resolve_left hparent0
    have hp := treeNode_deleteGeom s parent removed hg hremoved (Or.inr hparentAlloc)
    let parentIndex := (parent.toNat - 1) % 4
    by_cases hleftRaw :
        s.nodes[((treeNode s removed).parent.toNat - 1) % 4]!.left = removed
    · have hleft : s.nodes[parentIndex]!.left = removed := hleftRaw
      simp only [hleftRaw, if_pos]
      let parentLinked :=
        { s with
          nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with left := replacement } }
      have hgP : deleteGeom parentLinked :=
        deleteGeom_set s parentIndex { s.nodes[parentIndex]! with left := replacement }
          (Nat.mod_lt _ (by decide)) hg hreplacement hp.2.1 hp.2.2.1 hp.2.2.2
      by_cases hreplacement0 : replacement = 0
      · simpa [parentLinked, parentIndex, parent, removedNode, hparent0raw, hleftRaw,
          hreplacement0] using hgP
      · simp only [hreplacement0, if_neg]
        have hreplacementAlloc : allocated s replacement :=
          hreplacement.resolve_left hreplacement0
        have hreplacementP : allocated parentLinked replacement := by
          simpa only [parentLinked, allocated] using hreplacementAlloc
        have hremovedP : allocated parentLinked removed := by
          simpa only [parentLinked, allocated] using hremoved
        have hn := treeNode_deleteGeom parentLinked replacement removed hgP hremovedP
          (Or.inr hreplacementP)
        simpa [parentLinked, parentIndex, parent, removedNode, hparent0raw, hleftRaw,
            hreplacement0] using
          deleteGeom_set parentLinked ((replacement.toNat - 1) % 4)
            { parentLinked.nodes[(replacement.toNat - 1) % 4]! with parent := parent }
            (Nat.mod_lt _ (by decide)) hgP hn.1 hn.2.1
            (by simpa only [parentLinked, linkAllocated, allocated] using hparent)
            hn.2.2.2
    · have hleft : s.nodes[parentIndex]!.left ≠ removed := hleftRaw
      simp only [hleftRaw, if_neg]
      let parentLinked :=
        { s with
          nodes := s.nodes.set parentIndex { s.nodes[parentIndex]! with right := replacement } }
      have hgP : deleteGeom parentLinked :=
        deleteGeom_set s parentIndex { s.nodes[parentIndex]! with right := replacement }
          (Nat.mod_lt _ (by decide)) hg hp.1 hreplacement hp.2.2.1 hp.2.2.2
      by_cases hreplacement0 : replacement = 0
      · simpa [parentLinked, parentIndex, parent, removedNode, hparent0raw, hleftRaw,
          hreplacement0] using hgP
      · simp only [hreplacement0, if_neg]
        have hreplacementAlloc : allocated s replacement :=
          hreplacement.resolve_left hreplacement0
        have hreplacementP : allocated parentLinked replacement := by
          simpa only [parentLinked, allocated] using hreplacementAlloc
        have hremovedP : allocated parentLinked removed := by
          simpa only [parentLinked, allocated] using hremoved
        have hn := treeNode_deleteGeom parentLinked replacement removed hgP hremovedP
          (Or.inr hreplacementP)
        simpa [parentLinked, parentIndex, parent, removedNode, hparent0raw, hleftRaw,
            hreplacement0] using
          deleteGeom_set parentLinked ((replacement.toNat - 1) % 4)
            { parentLinked.nodes[(replacement.toNat - 1) % 4]! with parent := parent }
            (Nat.mod_lt _ (by decide)) hgP hn.1 hn.2.1
            (by simpa only [parentLinked, linkAllocated, allocated] using hparent)
            hn.2.2.2

private theorem transplantNode_wf (s : State) (removed replacement : UInt64)
    (hwf : wf s) (hlinks : linksAllocated s)
    (hremoved : allocated s removed) (hreplacement : linkAllocated s replacement) :
    wf (transplantNode s removed replacement) :=
  (transplantNode_deleteGeom s removed replacement ⟨hwf, hlinks⟩
    hremoved hreplacement).1

/-- 删除专用左旋只重写哨兵或已分配地址，保持删除几何。 -/
private theorem rotateLeftDelete_deleteGeom (s : State) (xAddress witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress) :
    deleteGeom (rotateLeftDelete s xAddress) := by
  let xi := (xAddress.toNat - 1) % 4
  let x := s.nodes[xi]!
  let yAddress := x.right
  have hx := treeNode_deleteGeom s xAddress witness hg hwitness hxAddress
  change linkAllocated s x.left ∧ linkAllocated s yAddress ∧
    linkAllocated s x.parent ∧ x.color ≤ 1 at hx
  by_cases hy0 : yAddress = 0
  · simpa [rotateLeftDelete, xi, x, yAddress, hy0] using hg
  · have hyAddress : allocated s yAddress := hx.2.1.resolve_left hy0
    let yi := (yAddress.toNat - 1) % 4
    let y := s.nodes[yi]!
    let innerAddress := y.left
    let parentAddress := x.parent
    have hy := treeNode_deleteGeom s yAddress witness hg hwitness (Or.inr hyAddress)
    change linkAllocated s innerAddress ∧ linkAllocated s y.right ∧
      linkAllocated s y.parent ∧ y.color ≤ 1 at hy
    let nodes1 :=
      s.nodes.set xi { x with right := innerAddress, parent := yAddress }
    have hg1 : deleteGeom { s with nodes := nodes1 } :=
      deleteGeom_set s xi { x with right := innerAddress, parent := yAddress }
        (Nat.mod_lt _ (by decide)) hg hx.1 hy.1 (Or.inr hyAddress) hx.2.2.2
    let nodes2 :=
      if innerAddress = 0 then nodes1
      else
        let innerIndex := (innerAddress.toNat - 1) % 4
        nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    have hg2 : deleteGeom { s with nodes := nodes2 } := by
      by_cases hinner0 : innerAddress = 0
      · simpa [nodes2, hinner0] using hg1
      · have hinner : allocated s innerAddress := hy.1.resolve_left hinner0
        have hinner1 : allocated { s with nodes := nodes1 } innerAddress := by
          simpa only [allocated] using hinner
        have hn := treeNode_deleteGeom { s with nodes := nodes1 } innerAddress witness
          hg1 (by simpa only [allocated] using hwitness) (Or.inr hinner1)
        simpa [nodes2, hinner0, treeNode] using
          deleteGeom_set { s with nodes := nodes1 } ((innerAddress.toNat - 1) % 4)
            { nodes1[(innerAddress.toNat - 1) % 4]! with parent := xAddress }
            (Nat.mod_lt _ (by decide)) hg1 hn.1 hn.2.1
            (by simpa only [linkAllocated, allocated] using hxAddress) hn.2.2.2
    let nodes3 :=
      if parentAddress = 0 then nodes2
      else
        let parentIndex := (parentAddress.toNat - 1) % 4
        if nodes2[parentIndex]!.left = xAddress then
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        else
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
    have hg3 : deleteGeom { s with nodes := nodes3 } := by
      by_cases hparent0 : parentAddress = 0
      · simpa [nodes3, hparent0] using hg2
      · have hparent : allocated s parentAddress := hx.2.2.1.resolve_left hparent0
        have hparent2 : allocated { s with nodes := nodes2 } parentAddress := by
          simpa only [allocated] using hparent
        have hp := treeNode_deleteGeom { s with nodes := nodes2 } parentAddress witness
          hg2 (by simpa only [allocated] using hwitness) (Or.inr hparent2)
        let parentIndex := (parentAddress.toNat - 1) % 4
        by_cases hleft : nodes2[parentIndex]!.left = xAddress
        · simpa [nodes3, hparent0, parentIndex, hleft, treeNode] using
            deleteGeom_set { s with nodes := nodes2 } parentIndex
              { nodes2[parentIndex]! with left := yAddress }
              (Nat.mod_lt _ (by decide)) hg2
              (by simpa only [linkAllocated, allocated] using (Or.inr hyAddress :
                linkAllocated s yAddress))
              hp.2.1 hp.2.2.1 hp.2.2.2
        · simpa [nodes3, hparent0, parentIndex, hleft, treeNode] using
            deleteGeom_set { s with nodes := nodes2 } parentIndex
              { nodes2[parentIndex]! with right := yAddress }
              (Nat.mod_lt _ (by decide)) hg2 hp.1
              (by simpa only [linkAllocated, allocated] using (Or.inr hyAddress :
                linkAllocated s yAddress))
              hp.2.2.1 hp.2.2.2
    let nodes4 :=
      nodes3.set yi { nodes3[yi]! with left := xAddress, parent := parentAddress }
    have hy3 : allocated { s with nodes := nodes3 } yAddress := by
      simpa only [allocated] using hyAddress
    have hyn := treeNode_deleteGeom { s with nodes := nodes3 } yAddress witness
      hg3 (by simpa only [allocated] using hwitness) (Or.inr hy3)
    have hg4 : deleteGeom { s with nodes := nodes4 } := by
      exact deleteGeom_set { s with nodes := nodes3 } yi
        { nodes3[yi]! with left := xAddress, parent := parentAddress }
        (Nat.mod_lt _ (by decide)) hg3
        (by simpa only [linkAllocated, allocated] using hxAddress)
        hyn.2.1
        (by simpa only [linkAllocated, allocated] using hx.2.2.1)
        hyn.2.2.2
    have hgRoot :=
      deleteGeom_root { s with nodes := nodes4 }
        (if parentAddress = 0 then yAddress else s.root) hg4
    simpa [rotateLeftDelete, xi, x, yAddress, hy0, yi, y, innerAddress,
      parentAddress, nodes1, nodes2, nodes3, nodes4] using hgRoot

private theorem rotateLeftDelete_wf (s : State) (xAddress witness : UInt64)
    (hwf : wf s) (hlinks : linksAllocated s) (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress) :
    wf (rotateLeftDelete s xAddress) :=
  (rotateLeftDelete_deleteGeom s xAddress witness ⟨hwf, hlinks⟩
    hwitness hxAddress).1

/-- 删除专用右旋是左旋的镜像，保持删除几何。 -/
private theorem rotateRightDelete_deleteGeom (s : State) (xAddress witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress) :
    deleteGeom (rotateRightDelete s xAddress) := by
  let xi := (xAddress.toNat - 1) % 4
  let x := s.nodes[xi]!
  let yAddress := x.left
  have hx := treeNode_deleteGeom s xAddress witness hg hwitness hxAddress
  change linkAllocated s yAddress ∧ linkAllocated s x.right ∧
    linkAllocated s x.parent ∧ x.color ≤ 1 at hx
  by_cases hy0 : yAddress = 0
  · simpa [rotateRightDelete, xi, x, yAddress, hy0] using hg
  · have hyAddress : allocated s yAddress := hx.1.resolve_left hy0
    let yi := (yAddress.toNat - 1) % 4
    let y := s.nodes[yi]!
    let innerAddress := y.right
    let parentAddress := x.parent
    have hy := treeNode_deleteGeom s yAddress witness hg hwitness (Or.inr hyAddress)
    change linkAllocated s y.left ∧ linkAllocated s innerAddress ∧
      linkAllocated s y.parent ∧ y.color ≤ 1 at hy
    let nodes1 :=
      s.nodes.set xi { x with left := innerAddress, parent := yAddress }
    have hg1 : deleteGeom { s with nodes := nodes1 } :=
      deleteGeom_set s xi { x with left := innerAddress, parent := yAddress }
        (Nat.mod_lt _ (by decide)) hg hy.2.1 hx.2.1 (Or.inr hyAddress) hx.2.2.2
    let nodes2 :=
      if innerAddress = 0 then nodes1
      else
        let innerIndex := (innerAddress.toNat - 1) % 4
        nodes1.set innerIndex { nodes1[innerIndex]! with parent := xAddress }
    have hg2 : deleteGeom { s with nodes := nodes2 } := by
      by_cases hinner0 : innerAddress = 0
      · simpa [nodes2, hinner0] using hg1
      · have hinner : allocated s innerAddress := hy.2.1.resolve_left hinner0
        have hinner1 : allocated { s with nodes := nodes1 } innerAddress := by
          simpa only [allocated] using hinner
        have hn := treeNode_deleteGeom { s with nodes := nodes1 } innerAddress witness
          hg1 (by simpa only [allocated] using hwitness) (Or.inr hinner1)
        simpa [nodes2, hinner0, treeNode] using
          deleteGeom_set { s with nodes := nodes1 } ((innerAddress.toNat - 1) % 4)
            { nodes1[(innerAddress.toNat - 1) % 4]! with parent := xAddress }
            (Nat.mod_lt _ (by decide)) hg1 hn.1 hn.2.1
            (by simpa only [linkAllocated, allocated] using hxAddress) hn.2.2.2
    let nodes3 :=
      if parentAddress = 0 then nodes2
      else
        let parentIndex := (parentAddress.toNat - 1) % 4
        if nodes2[parentIndex]!.left = xAddress then
          nodes2.set parentIndex { nodes2[parentIndex]! with left := yAddress }
        else
          nodes2.set parentIndex { nodes2[parentIndex]! with right := yAddress }
    have hg3 : deleteGeom { s with nodes := nodes3 } := by
      by_cases hparent0 : parentAddress = 0
      · simpa [nodes3, hparent0] using hg2
      · have hparent : allocated s parentAddress := hx.2.2.1.resolve_left hparent0
        have hparent2 : allocated { s with nodes := nodes2 } parentAddress := by
          simpa only [allocated] using hparent
        have hp := treeNode_deleteGeom { s with nodes := nodes2 } parentAddress witness
          hg2 (by simpa only [allocated] using hwitness) (Or.inr hparent2)
        let parentIndex := (parentAddress.toNat - 1) % 4
        by_cases hleft : nodes2[parentIndex]!.left = xAddress
        · simpa [nodes3, hparent0, parentIndex, hleft, treeNode] using
            deleteGeom_set { s with nodes := nodes2 } parentIndex
              { nodes2[parentIndex]! with left := yAddress }
              (Nat.mod_lt _ (by decide)) hg2
              (by simpa only [linkAllocated, allocated] using (Or.inr hyAddress :
                linkAllocated s yAddress))
              hp.2.1 hp.2.2.1 hp.2.2.2
        · simpa [nodes3, hparent0, parentIndex, hleft, treeNode] using
            deleteGeom_set { s with nodes := nodes2 } parentIndex
              { nodes2[parentIndex]! with right := yAddress }
              (Nat.mod_lt _ (by decide)) hg2 hp.1
              (by simpa only [linkAllocated, allocated] using (Or.inr hyAddress :
                linkAllocated s yAddress))
              hp.2.2.1 hp.2.2.2
    let nodes4 :=
      nodes3.set yi { nodes3[yi]! with right := xAddress, parent := parentAddress }
    have hy3 : allocated { s with nodes := nodes3 } yAddress := by
      simpa only [allocated] using hyAddress
    have hyn := treeNode_deleteGeom { s with nodes := nodes3 } yAddress witness
      hg3 (by simpa only [allocated] using hwitness) (Or.inr hy3)
    have hg4 : deleteGeom { s with nodes := nodes4 } := by
      exact deleteGeom_set { s with nodes := nodes3 } yi
        { nodes3[yi]! with right := xAddress, parent := parentAddress }
        (Nat.mod_lt _ (by decide)) hg3 hyn.1
        (by simpa only [linkAllocated, allocated] using hxAddress)
        (by simpa only [linkAllocated, allocated] using hx.2.2.1)
        hyn.2.2.2
    have hgRoot :=
      deleteGeom_root { s with nodes := nodes4 }
        (if parentAddress = 0 then yAddress else s.root) hg4
    simpa [rotateRightDelete, xi, x, yAddress, hy0, yi, y, innerAddress,
      parentAddress, nodes1, nodes2, nodes3, nodes4] using hgRoot

private theorem rotateRightDelete_wf (s : State) (xAddress witness : UInt64)
    (hwf : wf s) (hlinks : linksAllocated s) (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress) :
    wf (rotateRightDelete s xAddress) :=
  (rotateRightDelete_deleteGeom s xAddress witness ⟨hwf, hlinks⟩
    hwitness hxAddress).1

/-- successor 搬移由 transplant/link/paint 组合而成，组合保持删除几何。 -/
private theorem moveSuccessor_deleteGeom (s : State)
    (removed successor replacement : UInt64)
    (hg : deleteGeom s) (hremoved : allocated s removed)
    (hsuccessor : allocated s successor)
    (hreplacement : linkAllocated s replacement) :
    deleteGeom (moveSuccessor s removed successor replacement) := by
  let removedNode := treeNode s removed
  let successorNode := treeNode s successor
  have hr := treeNode_deleteGeom s removed removed hg hremoved (Or.inr hremoved)
  change linkAllocated s removedNode.left ∧ linkAllocated s removedNode.right ∧
    linkAllocated s removedNode.parent ∧ removedNode.color ≤ 1 at hr
  unfold moveSuccessor
  dsimp only
  by_cases hdirectRaw : (treeNode s successor).parent = removed
  · simp only [hdirectRaw, if_pos]
    let moved := transplantNode s removed successor
    have hgMoved : deleteGeom moved :=
      transplantNode_deleteGeom s removed successor hg hremoved (Or.inr hsuccessor)
    have hremovedMoved : allocated moved removed := by
      exact allocated_of_bump_eq hremoved (transplantNode_bumpIndex s removed successor)
    have hsuccessorMoved : allocated moved successor := by
      exact allocated_of_bump_eq hsuccessor (transplantNode_bumpIndex s removed successor)
    have hleftMoved : linkAllocated moved removedNode.left := by
      exact linkAllocated_of_bump_eq hr.1 (transplantNode_bumpIndex s removed successor)
    let withLeft := linkLeft moved successor removedNode.left
    have hgLeft : deleteGeom withLeft :=
      linkLeft_deleteGeom moved successor removedNode.left removed hgMoved hremovedMoved
        hsuccessorMoved hleftMoved
    exact paintNode_deleteGeom withLeft successor removedNode.color hgLeft hr.2.2.2
  · simp only [hdirectRaw, if_neg]
    let detached := transplantNode s successor replacement
    have hgDetached : deleteGeom detached :=
      transplantNode_deleteGeom s successor replacement hg hsuccessor hreplacement
    have hremovedDetached : allocated detached removed := by
      exact allocated_of_bump_eq hremoved
        (transplantNode_bumpIndex s successor replacement)
    have hsuccessorDetached : allocated detached successor := by
      exact allocated_of_bump_eq hsuccessor
        (transplantNode_bumpIndex s successor replacement)
    have hrightDetached : linkAllocated detached removedNode.right := by
      exact linkAllocated_of_bump_eq hr.2.1
        (transplantNode_bumpIndex s successor replacement)
    let withRight := linkRight detached successor removedNode.right
    have hgRight : deleteGeom withRight :=
      linkRight_deleteGeom detached successor removedNode.right removed hgDetached
        hremovedDetached hsuccessorDetached hrightDetached
    have hremovedRight : allocated withRight removed := by
      exact allocated_of_bump_eq hremovedDetached
        (linkRight_bumpIndex detached successor removedNode.right)
    have hsuccessorRight : allocated withRight successor := by
      exact allocated_of_bump_eq hsuccessorDetached
        (linkRight_bumpIndex detached successor removedNode.right)
    let moved := transplantNode withRight removed successor
    have hgMoved : deleteGeom moved :=
      transplantNode_deleteGeom withRight removed successor hgRight hremovedRight
        (Or.inr hsuccessorRight)
    have hremovedMoved : allocated moved removed := by
      exact allocated_of_bump_eq hremovedRight
        (transplantNode_bumpIndex withRight removed successor)
    have hsuccessorMoved : allocated moved successor := by
      exact allocated_of_bump_eq hsuccessorRight
        (transplantNode_bumpIndex withRight removed successor)
    have hleftMoved : linkAllocated moved removedNode.left := by
      exact linkAllocated_of_bump_eq
        (linkAllocated_of_bump_eq
          (linkAllocated_of_bump_eq hr.1
            (transplantNode_bumpIndex s successor replacement))
          (linkRight_bumpIndex detached successor removedNode.right))
        (transplantNode_bumpIndex withRight removed successor)
    let withLeft := linkLeft moved successor removedNode.left
    have hgLeft : deleteGeom withLeft :=
      linkLeft_deleteGeom moved successor removedNode.left removed hgMoved hremovedMoved
        hsuccessorMoved hleftMoved
    exact paintNode_deleteGeom withLeft successor removedNode.color hgLeft hr.2.2.2

private theorem moveSuccessor_wf (s : State)
    (removed successor replacement : UInt64)
    (hwf : wf s) (hlinks : linksAllocated s)
    (hremoved : allocated s removed) (hsuccessor : allocated s successor)
    (hreplacement : linkAllocated s replacement) :
    wf (moveSuccessor s removed successor replacement) :=
  (moveSuccessor_deleteGeom s removed successor replacement ⟨hwf, hlinks⟩
    hremoved hsuccessor hreplacement).1

/-- `fixDeleted` 的 x 为左孩子时，覆盖红兄弟、双黑孩子与近/远侄子三类分支。 -/
private theorem fixDeleted_left_deleteGeom (s : State)
    (xAddress parentAddress witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hparent : allocated s parentAddress) :
    deleteGeom
      (let firstSibling := (treeNode s parentAddress).right
       let afterRedSibling :=
         if treeColor s firstSibling = 1 then
           let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
           rotateLeftDelete recolored parentAddress
         else s
       let sibling := (treeNode afterRedSibling parentAddress).right
       let nearChild := (treeNode afterRedSibling sibling).left
       let farChild := (treeNode afterRedSibling sibling).right
       if treeColor afterRedSibling nearChild = 0 &&
           treeColor afterRedSibling farChild = 0 then
         let siblingRed := paintNode afterRedSibling sibling 1
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
         rotateLeftDelete recolored parentAddress) := by
  have hp := treeNode_deleteGeom s parentAddress witness hg hwitness (Or.inr hparent)
  let firstSibling := (treeNode s parentAddress).right
  have hfirst : linkAllocated s firstSibling := hp.2.1
  let afterRedSibling :=
    if treeColor s firstSibling = 1 then
      let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
      rotateLeftDelete recolored parentAddress
    else s
  have hafter : deleteGeom afterRedSibling ∧
      afterRedSibling.bumpIndex = s.bumpIndex := by
    by_cases hred : treeColor s firstSibling = 1
    · let paintedSibling := paintNode s firstSibling 0
      have hgSibling := paintNode_deleteGeom s firstSibling 0 hg (by decide)
      let recolored := paintNode paintedSibling parentAddress 1
      have hgRecolored :=
        paintNode_deleteGeom paintedSibling parentAddress 1 hgSibling (by decide)
      have hwitnessRecolored : allocated recolored witness := by
        exact allocated_of_bump_eq
          (allocated_of_bump_eq hwitness (paintNode_bumpIndex s firstSibling 0))
          (paintNode_bumpIndex paintedSibling parentAddress 1)
      have hparentRecolored : allocated recolored parentAddress := by
        exact allocated_of_bump_eq
          (allocated_of_bump_eq hparent (paintNode_bumpIndex s firstSibling 0))
          (paintNode_bumpIndex paintedSibling parentAddress 1)
      have hgRotated :=
        rotateLeftDelete_deleteGeom recolored parentAddress witness hgRecolored
          hwitnessRecolored (Or.inr hparentRecolored)
      constructor
      · simpa [afterRedSibling, hred, recolored, paintedSibling] using hgRotated
      · calc
          afterRedSibling.bumpIndex =
              (rotateLeftDelete recolored parentAddress).bumpIndex := by
                simp [afterRedSibling, hred, recolored, paintedSibling]
          _ = recolored.bumpIndex :=
            rotateLeftDelete_bumpIndex recolored parentAddress
          _ = paintedSibling.bumpIndex := paintNode_bumpIndex paintedSibling parentAddress 1
          _ = s.bumpIndex := paintNode_bumpIndex s firstSibling 0
    · constructor
      · simpa [afterRedSibling, hred] using hg
      · simp [afterRedSibling, hred]
  have hwitnessAfter : allocated afterRedSibling witness :=
    allocated_of_bump_eq hwitness hafter.2
  have hparentAfter : allocated afterRedSibling parentAddress :=
    allocated_of_bump_eq hparent hafter.2
  let sibling := (treeNode afterRedSibling parentAddress).right
  have hpAfter := treeNode_deleteGeom afterRedSibling parentAddress witness hafter.1
    hwitnessAfter (Or.inr hparentAfter)
  have hsibling : linkAllocated afterRedSibling sibling := hpAfter.2.1
  let nearChild := (treeNode afterRedSibling sibling).left
  let farChild := (treeNode afterRedSibling sibling).right
  have hsiblingNode := treeNode_deleteGeom afterRedSibling sibling witness hafter.1
    hwitnessAfter hsibling
  change linkAllocated afterRedSibling nearChild ∧
    linkAllocated afterRedSibling farChild ∧
    linkAllocated afterRedSibling (treeNode afterRedSibling sibling).parent ∧
    (treeNode afterRedSibling sibling).color ≤ 1 at hsiblingNode
  change deleteGeom
    (if treeColor afterRedSibling nearChild = 0 &&
        treeColor afterRedSibling farChild = 0 then
      paintNode (paintNode afterRedSibling sibling 1) parentAddress 0
    else
      let aligned :=
        if treeColor afterRedSibling farChild = 0 then
          rotateRightDelete
            (paintNode (paintNode afterRedSibling nearChild 0) sibling 1) sibling
        else afterRedSibling
      let alignedSibling := (treeNode aligned parentAddress).right
      let alignedFar := (treeNode aligned alignedSibling).right
      let parentColor := treeColor aligned parentAddress
      let recolored :=
        paintNode
          (paintNode (paintNode aligned alignedSibling parentColor) parentAddress 0)
          alignedFar 0
      rotateLeftDelete recolored parentAddress)
  by_cases hblack :
      treeColor afterRedSibling nearChild = 0 &&
        treeColor afterRedSibling farChild = 0
  · simp only [hblack, if_pos]
    let siblingRed := paintNode afterRedSibling sibling 1
    have hgSibling :=
      paintNode_deleteGeom afterRedSibling sibling 1 hafter.1 (by decide)
    change deleteGeom (paintNode siblingRed parentAddress 0)
    exact paintNode_deleteGeom siblingRed parentAddress 0 hgSibling (by decide)
  · simp only [hblack, if_neg]
    let aligned :=
      if treeColor afterRedSibling farChild = 0 then
        let recolored :=
          paintNode (paintNode afterRedSibling nearChild 0) sibling 1
        rotateRightDelete recolored sibling
      else afterRedSibling
    have haligned : deleteGeom aligned ∧
        aligned.bumpIndex = afterRedSibling.bumpIndex := by
      by_cases hfar : treeColor afterRedSibling farChild = 0
      · let paintedNear := paintNode afterRedSibling nearChild 0
        have hgNear :=
          paintNode_deleteGeom afterRedSibling nearChild 0 hafter.1 (by decide)
        let recolored := paintNode paintedNear sibling 1
        have hgRecolored :=
          paintNode_deleteGeom paintedNear sibling 1 hgNear (by decide)
        have hwitnessRecolored : allocated recolored witness := by
          exact allocated_of_bump_eq
            (allocated_of_bump_eq hwitnessAfter
              (paintNode_bumpIndex afterRedSibling nearChild 0))
            (paintNode_bumpIndex paintedNear sibling 1)
        have hsiblingRecolored : linkAllocated recolored sibling := by
          exact linkAllocated_of_bump_eq
            (linkAllocated_of_bump_eq hsibling
              (paintNode_bumpIndex afterRedSibling nearChild 0))
            (paintNode_bumpIndex paintedNear sibling 1)
        have hgRotated :=
          rotateRightDelete_deleteGeom recolored sibling witness hgRecolored
            hwitnessRecolored hsiblingRecolored
        constructor
        · simpa [aligned, hfar, recolored, paintedNear] using hgRotated
        · calc
            aligned.bumpIndex =
                (rotateRightDelete recolored sibling).bumpIndex := by
                  simp [aligned, hfar, recolored, paintedNear]
            _ = recolored.bumpIndex :=
              rotateRightDelete_bumpIndex recolored sibling
            _ = paintedNear.bumpIndex := paintNode_bumpIndex paintedNear sibling 1
            _ = afterRedSibling.bumpIndex :=
              paintNode_bumpIndex afterRedSibling nearChild 0
      · constructor
        · simpa [aligned, hfar] using hafter.1
        · simp [aligned, hfar]
    have hwitnessAligned : allocated aligned witness :=
      allocated_of_bump_eq hwitnessAfter haligned.2
    have hparentAligned : allocated aligned parentAddress :=
      allocated_of_bump_eq hparentAfter haligned.2
    let alignedSibling := (treeNode aligned parentAddress).right
    have hpAligned := treeNode_deleteGeom aligned parentAddress witness haligned.1
      hwitnessAligned (Or.inr hparentAligned)
    have hAlignedSibling : linkAllocated aligned alignedSibling := hpAligned.2.1
    let alignedFar := (treeNode aligned alignedSibling).right
    have hsAligned := treeNode_deleteGeom aligned alignedSibling witness haligned.1
      hwitnessAligned hAlignedSibling
    have hAlignedFar : linkAllocated aligned alignedFar := hsAligned.2.1
    let parentColor := treeColor aligned parentAddress
    have hparentColor : parentColor ≤ 1 := by
      unfold parentColor treeColor
      split
      · decide
      · exact hpAligned.2.2.2
    let paintedSibling := paintNode aligned alignedSibling parentColor
    have hgPaintedSibling :=
      paintNode_deleteGeom aligned alignedSibling parentColor haligned.1 hparentColor
    let paintedParent := paintNode paintedSibling parentAddress 0
    have hgPaintedParent :=
      paintNode_deleteGeom paintedSibling parentAddress 0 hgPaintedSibling (by decide)
    let recolored := paintNode paintedParent alignedFar 0
    have hgRecolored :=
      paintNode_deleteGeom paintedParent alignedFar 0 hgPaintedParent (by decide)
    have hwitnessRecolored : allocated recolored witness := by
      exact allocated_of_bump_eq
        (allocated_of_bump_eq
          (allocated_of_bump_eq hwitnessAligned
            (paintNode_bumpIndex aligned alignedSibling parentColor))
          (paintNode_bumpIndex paintedSibling parentAddress 0))
        (paintNode_bumpIndex paintedParent alignedFar 0)
    have hparentRecolored : allocated recolored parentAddress := by
      exact allocated_of_bump_eq
        (allocated_of_bump_eq
          (allocated_of_bump_eq hparentAligned
            (paintNode_bumpIndex aligned alignedSibling parentColor))
          (paintNode_bumpIndex paintedSibling parentAddress 0))
        (paintNode_bumpIndex paintedParent alignedFar 0)
    change deleteGeom (rotateLeftDelete recolored parentAddress)
    exact rotateLeftDelete_deleteGeom recolored parentAddress witness hgRecolored
      hwitnessRecolored (Or.inr hparentRecolored)

/-- `fixDeleted` 的 x 为右孩子时的镜像分支。 -/
private theorem fixDeleted_right_deleteGeom (s : State)
    (xAddress parentAddress witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hparent : allocated s parentAddress) :
    deleteGeom
      (let firstSibling := (treeNode s parentAddress).left
       let afterRedSibling :=
         if treeColor s firstSibling = 1 then
           let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
           rotateRightDelete recolored parentAddress
         else s
       let sibling := (treeNode afterRedSibling parentAddress).left
       let nearChild := (treeNode afterRedSibling sibling).right
       let farChild := (treeNode afterRedSibling sibling).left
       if treeColor afterRedSibling nearChild = 0 &&
           treeColor afterRedSibling farChild = 0 then
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
         rotateRightDelete recolored parentAddress) := by
  have hp := treeNode_deleteGeom s parentAddress witness hg hwitness (Or.inr hparent)
  let firstSibling := (treeNode s parentAddress).left
  have hfirst : linkAllocated s firstSibling := hp.1
  let afterRedSibling :=
    if treeColor s firstSibling = 1 then
      let recolored := paintNode (paintNode s firstSibling 0) parentAddress 1
      rotateRightDelete recolored parentAddress
    else s
  have hafter : deleteGeom afterRedSibling ∧
      afterRedSibling.bumpIndex = s.bumpIndex := by
    by_cases hred : treeColor s firstSibling = 1
    · let paintedSibling := paintNode s firstSibling 0
      have hgSibling := paintNode_deleteGeom s firstSibling 0 hg (by decide)
      let recolored := paintNode paintedSibling parentAddress 1
      have hgRecolored :=
        paintNode_deleteGeom paintedSibling parentAddress 1 hgSibling (by decide)
      have hwitnessRecolored : allocated recolored witness := by
        exact allocated_of_bump_eq
          (allocated_of_bump_eq hwitness (paintNode_bumpIndex s firstSibling 0))
          (paintNode_bumpIndex paintedSibling parentAddress 1)
      have hparentRecolored : allocated recolored parentAddress := by
        exact allocated_of_bump_eq
          (allocated_of_bump_eq hparent (paintNode_bumpIndex s firstSibling 0))
          (paintNode_bumpIndex paintedSibling parentAddress 1)
      have hgRotated :=
        rotateRightDelete_deleteGeom recolored parentAddress witness hgRecolored
          hwitnessRecolored (Or.inr hparentRecolored)
      constructor
      · simpa [afterRedSibling, hred, recolored, paintedSibling] using hgRotated
      · calc
          afterRedSibling.bumpIndex =
              (rotateRightDelete recolored parentAddress).bumpIndex := by
                simp [afterRedSibling, hred, recolored, paintedSibling]
          _ = recolored.bumpIndex :=
            rotateRightDelete_bumpIndex recolored parentAddress
          _ = paintedSibling.bumpIndex := paintNode_bumpIndex paintedSibling parentAddress 1
          _ = s.bumpIndex := paintNode_bumpIndex s firstSibling 0
    · constructor
      · simpa [afterRedSibling, hred] using hg
      · simp [afterRedSibling, hred]
  have hwitnessAfter : allocated afterRedSibling witness :=
    allocated_of_bump_eq hwitness hafter.2
  have hparentAfter : allocated afterRedSibling parentAddress :=
    allocated_of_bump_eq hparent hafter.2
  let sibling := (treeNode afterRedSibling parentAddress).left
  have hpAfter := treeNode_deleteGeom afterRedSibling parentAddress witness hafter.1
    hwitnessAfter (Or.inr hparentAfter)
  have hsibling : linkAllocated afterRedSibling sibling := hpAfter.1
  let nearChild := (treeNode afterRedSibling sibling).right
  let farChild := (treeNode afterRedSibling sibling).left
  have hsiblingNode := treeNode_deleteGeom afterRedSibling sibling witness hafter.1
    hwitnessAfter hsibling
  change linkAllocated afterRedSibling farChild ∧
    linkAllocated afterRedSibling nearChild ∧
    linkAllocated afterRedSibling (treeNode afterRedSibling sibling).parent ∧
    (treeNode afterRedSibling sibling).color ≤ 1 at hsiblingNode
  change deleteGeom
    (if treeColor afterRedSibling nearChild = 0 &&
        treeColor afterRedSibling farChild = 0 then
      paintNode (paintNode afterRedSibling sibling 1) parentAddress 0
    else
      let aligned :=
        if treeColor afterRedSibling farChild = 0 then
          rotateLeftDelete
            (paintNode (paintNode afterRedSibling nearChild 0) sibling 1) sibling
        else afterRedSibling
      let alignedSibling := (treeNode aligned parentAddress).left
      let alignedFar := (treeNode aligned alignedSibling).left
      let parentColor := treeColor aligned parentAddress
      let recolored :=
        paintNode
          (paintNode (paintNode aligned alignedSibling parentColor) parentAddress 0)
          alignedFar 0
      rotateRightDelete recolored parentAddress)
  by_cases hblack :
      treeColor afterRedSibling nearChild = 0 &&
        treeColor afterRedSibling farChild = 0
  · simp only [hblack, if_pos]
    let siblingRed := paintNode afterRedSibling sibling 1
    have hgSibling :=
      paintNode_deleteGeom afterRedSibling sibling 1 hafter.1 (by decide)
    change deleteGeom (paintNode siblingRed parentAddress 0)
    exact paintNode_deleteGeom siblingRed parentAddress 0 hgSibling (by decide)
  · simp only [hblack, if_neg]
    let aligned :=
      if treeColor afterRedSibling farChild = 0 then
        let recolored :=
          paintNode (paintNode afterRedSibling nearChild 0) sibling 1
        rotateLeftDelete recolored sibling
      else afterRedSibling
    have haligned : deleteGeom aligned ∧
        aligned.bumpIndex = afterRedSibling.bumpIndex := by
      by_cases hfar : treeColor afterRedSibling farChild = 0
      · let paintedNear := paintNode afterRedSibling nearChild 0
        have hgNear :=
          paintNode_deleteGeom afterRedSibling nearChild 0 hafter.1 (by decide)
        let recolored := paintNode paintedNear sibling 1
        have hgRecolored :=
          paintNode_deleteGeom paintedNear sibling 1 hgNear (by decide)
        have hwitnessRecolored : allocated recolored witness := by
          exact allocated_of_bump_eq
            (allocated_of_bump_eq hwitnessAfter
              (paintNode_bumpIndex afterRedSibling nearChild 0))
            (paintNode_bumpIndex paintedNear sibling 1)
        have hsiblingRecolored : linkAllocated recolored sibling := by
          exact linkAllocated_of_bump_eq
            (linkAllocated_of_bump_eq hsibling
              (paintNode_bumpIndex afterRedSibling nearChild 0))
            (paintNode_bumpIndex paintedNear sibling 1)
        have hgRotated :=
          rotateLeftDelete_deleteGeom recolored sibling witness hgRecolored
            hwitnessRecolored hsiblingRecolored
        constructor
        · simpa [aligned, hfar, recolored, paintedNear] using hgRotated
        · calc
            aligned.bumpIndex =
                (rotateLeftDelete recolored sibling).bumpIndex := by
                  simp [aligned, hfar, recolored, paintedNear]
            _ = recolored.bumpIndex :=
              rotateLeftDelete_bumpIndex recolored sibling
            _ = paintedNear.bumpIndex := paintNode_bumpIndex paintedNear sibling 1
            _ = afterRedSibling.bumpIndex :=
              paintNode_bumpIndex afterRedSibling nearChild 0
      · constructor
        · simpa [aligned, hfar] using hafter.1
        · simp [aligned, hfar]
    have hwitnessAligned : allocated aligned witness :=
      allocated_of_bump_eq hwitnessAfter haligned.2
    have hparentAligned : allocated aligned parentAddress :=
      allocated_of_bump_eq hparentAfter haligned.2
    let alignedSibling := (treeNode aligned parentAddress).left
    have hpAligned := treeNode_deleteGeom aligned parentAddress witness haligned.1
      hwitnessAligned (Or.inr hparentAligned)
    have hAlignedSibling : linkAllocated aligned alignedSibling := hpAligned.1
    let alignedFar := (treeNode aligned alignedSibling).left
    have hsAligned := treeNode_deleteGeom aligned alignedSibling witness haligned.1
      hwitnessAligned hAlignedSibling
    have hAlignedFar : linkAllocated aligned alignedFar := hsAligned.1
    let parentColor := treeColor aligned parentAddress
    have hparentColor : parentColor ≤ 1 := by
      unfold parentColor treeColor
      split
      · decide
      · exact hpAligned.2.2.2
    let paintedSibling := paintNode aligned alignedSibling parentColor
    have hgPaintedSibling :=
      paintNode_deleteGeom aligned alignedSibling parentColor haligned.1 hparentColor
    let paintedParent := paintNode paintedSibling parentAddress 0
    have hgPaintedParent :=
      paintNode_deleteGeom paintedSibling parentAddress 0 hgPaintedSibling (by decide)
    let recolored := paintNode paintedParent alignedFar 0
    have hgRecolored :=
      paintNode_deleteGeom paintedParent alignedFar 0 hgPaintedParent (by decide)
    have hwitnessRecolored : allocated recolored witness := by
      exact allocated_of_bump_eq
        (allocated_of_bump_eq
          (allocated_of_bump_eq hwitnessAligned
            (paintNode_bumpIndex aligned alignedSibling parentColor))
          (paintNode_bumpIndex paintedSibling parentAddress 0))
        (paintNode_bumpIndex paintedParent alignedFar 0)
    have hparentRecolored : allocated recolored parentAddress := by
      exact allocated_of_bump_eq
        (allocated_of_bump_eq
          (allocated_of_bump_eq hparentAligned
            (paintNode_bumpIndex aligned alignedSibling parentColor))
          (paintNode_bumpIndex paintedSibling parentAddress 0))
        (paintNode_bumpIndex paintedParent alignedFar 0)
    change deleteGeom (rotateRightDelete recolored parentAddress)
    exact rotateRightDelete_deleteGeom recolored parentAddress witness hgRecolored
      hwitnessRecolored (Or.inr hparentRecolored)

/-- 完整删除 fixup 保持几何；parent/x 均可为哨兵，否则必须已分配。 -/
private theorem fixDeleted_deleteGeom (s : State)
    (xAddress parentAddress witness : UInt64)
    (hg : deleteGeom s) (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress)
    (hparentAddress : linkAllocated s parentAddress) :
    deleteGeom (fixDeleted s xAddress parentAddress) := by
  unfold fixDeleted
  dsimp only
  split
  · exact paintNode_deleteGeom s xAddress 0 hg (by decide)
  · split
    · exact paintNode_deleteGeom s xAddress 0 hg (by decide)
    · split
      · exact paintNode_deleteGeom s xAddress 0 hg (by decide)
      · rename_i _ _ hparent0
        have hparent : allocated s parentAddress :=
          hparentAddress.resolve_left hparent0
        split
        · exact fixDeleted_left_deleteGeom s xAddress parentAddress witness
            hg hwitness hparent
        · exact fixDeleted_right_deleteGeom s xAddress parentAddress witness
            hg hwitness hparent

private theorem fixDeleted_wf (s : State)
    (xAddress parentAddress witness : UInt64)
    (hwf : wf s) (hlinks : linksAllocated s)
    (hwitness : allocated s witness)
    (hxAddress : linkAllocated s xAddress)
    (hparentAddress : linkAllocated s parentAddress) :
    wf (fixDeleted s xAddress parentAddress) :=
  (fixDeleted_deleteGeom s xAddress parentAddress witness ⟨hwf, hlinks⟩
    hwitness hxAddress hparentAddress).1

private theorem moveSuccessor_bumpIndex (s : State)
    (removed successor replacement : UInt64) :
    (moveSuccessor s removed successor replacement).bumpIndex = s.bumpIndex := by
  unfold moveSuccessor
  dsimp only
  split <;>
    simp only [paintNode_bumpIndex, linkLeft_bumpIndex, linkRight_bumpIndex,
      transplantNode_bumpIndex]

private theorem fixDeleted_bumpIndex (s : State) (xAddress parentAddress : UInt64) :
    (fixDeleted s xAddress parentAddress).bumpIndex = s.bumpIndex := by
  unfold fixDeleted
  repeat (first
    | split
    | simp only [paintNode_bumpIndex, rotateLeftDelete_bumpIndex,
        rotateRightDelete_bumpIndex]
    | rfl)

private theorem releaseRemoved_delete_wf (s : State) (addr : UInt64)
    (hwf : wf s) (ha : 1 ≤ addr ∧ addr < s.bumpIndex)
    (hsz0 : (0 : Nat) < s.size.toNat) : wf (releaseRemoved s addr) := by
  unfold releaseRemoved
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have ha0n : (1 : Nat) ≤ addr.toNat := ha.1
  have ha1n : addr.toNat < s.bumpIndex.toNat := ha.2
  have hb5n : s.bumpIndex.toNat ≤ 5 := hb5
  have haddr5 : addr.toNat ≤ 5 := by omega
  refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
  · show (s.size - 1).toNat ≤ 4
    have hsz' : s.size.toNat ≤ 4 := hsz
    have hsub : (s.size - 1).toNat ≤ s.size.toNat := by
      have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
      rw [UInt64.toNat_sub]
      have : (1 : Nat) ≤ s.size.toNat := hsz0
      have hone : UInt64.toNat 1 = 1 := rfl
      simp only [hone, h2]
      have hszlt : s.size.toNat < 4294967296 * 4294967296 :=
        UInt64.toNat_lt_size _
      omega
    omega
  · exact haddr5
  · exact Nat.le_of_lt ha.2
  · intro a ha0 ha1
    have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hi4 : (addr.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hia : (addr.toNat - 1) % 4 = (a.toNat - 1) % 4
    · have hget : (s.nodes.set ((addr.toNat - 1) % 4)
          { s.nodes[(addr.toNat - 1) % 4]! with
            left := s.freeHead, right := 0, parent := 0, color := 0 } hi4)[
          (a.toNat - 1) % 4]! =
          { s.nodes[(addr.toNat - 1) % 4]! with
            left := s.freeHead, right := 0, parent := 0, color := 0 } := by
        rw [← hia, vec_set_self]
      rw [hget]
      exact ⟨hfb, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    · rw [vec_set_ne s.nodes ((addr.toNat - 1) % 4) ((a.toNat - 1) % 4)
        { s.nodes[(addr.toNat - 1) % 4]! with
          left := s.freeHead, right := 0, parent := 0, color := 0 }
        hi4 hia hslot]
      exact hptr a ha0 ha1

/-- `removeNode` 的结构搬移、fixup、根染黑与释放四段组合保持基础 `wf`。 -/
private theorem removePipeline_wf (s : State)
    (removedAddress successorAddress replacementAddress replacementParent
      removedColor : UInt64)
    (hg : deleteGeom s) (hremoved : allocated s removedAddress)
    (hsuccessor : allocated s successorAddress)
    (hreplacement : linkAllocated s replacementAddress)
    (hreplacementParent : linkAllocated s replacementParent)
    (hsz0 : (0 : Nat) < s.size.toNat) :
    wf
      (let removed := treeNode s removedAddress
       let moved :=
         if removed.left = 0 then
           transplantNode s removedAddress removed.right
         else if removed.right = 0 then
           transplantNode s removedAddress removed.left
         else
           moveSuccessor s removedAddress successorAddress replacementAddress
       let fixed :=
         if removedColor = 0 then
           fixDeleted moved replacementAddress replacementParent
         else moved
       let rootBlackState := paintNode fixed fixed.root 0
       releaseRemoved rootBlackState removedAddress) := by
  let removed := treeNode s removedAddress
  have hr := treeNode_deleteGeom s removedAddress removedAddress hg hremoved
    (Or.inr hremoved)
  change linkAllocated s removed.left ∧ linkAllocated s removed.right ∧
    linkAllocated s removed.parent ∧ removed.color ≤ 1 at hr
  let moved :=
    if removed.left = 0 then
      transplantNode s removedAddress removed.right
    else if removed.right = 0 then
      transplantNode s removedAddress removed.left
    else
      moveSuccessor s removedAddress successorAddress replacementAddress
  have hmoved : deleteGeom moved ∧ moved.bumpIndex = s.bumpIndex ∧
      moved.size = s.size := by
    by_cases hleft0 : removed.left = 0
    · have hgMoved :=
        transplantNode_deleteGeom s removedAddress removed.right hg hremoved hr.2.1
      refine ⟨?_, ?_, ?_⟩
      · simpa [moved, hleft0] using hgMoved
      · simpa [moved, hleft0] using
          transplantNode_bumpIndex s removedAddress removed.right
      · simpa [moved, hleft0] using
          transplantNode_size s removedAddress removed.right
    · by_cases hright0 : removed.right = 0
      · have hgMoved :=
          transplantNode_deleteGeom s removedAddress removed.left hg hremoved hr.1
        refine ⟨?_, ?_, ?_⟩
        · simpa [moved, hleft0, hright0] using hgMoved
        · simpa [moved, hleft0, hright0] using
            transplantNode_bumpIndex s removedAddress removed.left
        · simpa [moved, hleft0, hright0] using
            transplantNode_size s removedAddress removed.left
      · have hgMoved :=
          moveSuccessor_deleteGeom s removedAddress successorAddress replacementAddress
            hg hremoved hsuccessor hreplacement
        refine ⟨?_, ?_, ?_⟩
        · simpa [moved, hleft0, hright0] using hgMoved
        · simpa [moved, hleft0, hright0] using
            moveSuccessor_bumpIndex s removedAddress successorAddress replacementAddress
        · simpa [moved, hleft0, hright0] using
            moveSuccessor_size s removedAddress successorAddress replacementAddress
  have hremovedMoved : allocated moved removedAddress :=
    allocated_of_bump_eq hremoved hmoved.2.1
  have hreplacementMoved : linkAllocated moved replacementAddress :=
    linkAllocated_of_bump_eq hreplacement hmoved.2.1
  have hparentMoved : linkAllocated moved replacementParent :=
    linkAllocated_of_bump_eq hreplacementParent hmoved.2.1
  let fixed :=
    if removedColor = 0 then
      fixDeleted moved replacementAddress replacementParent
    else moved
  have hfixed : deleteGeom fixed ∧ fixed.bumpIndex = moved.bumpIndex ∧
      fixed.size = moved.size := by
    by_cases hblack : removedColor = 0
    · have hgFixed :=
        fixDeleted_deleteGeom moved replacementAddress replacementParent removedAddress
          hmoved.1 hremovedMoved hreplacementMoved hparentMoved
      refine ⟨?_, ?_, ?_⟩
      · simpa [fixed, hblack] using hgFixed
      · simpa [fixed, hblack] using
          fixDeleted_bumpIndex moved replacementAddress replacementParent
      · simpa [fixed, hblack] using
          fixDeleted_size moved replacementAddress replacementParent
    · exact ⟨by simpa [fixed, hblack] using hmoved.1,
        by simp [fixed, hblack], by simp [fixed, hblack]⟩
  let rootBlackState := paintNode fixed fixed.root 0
  have hgRoot : deleteGeom rootBlackState :=
    paintNode_deleteGeom fixed fixed.root 0 hfixed.1 (by decide)
  have hremovedFixed : allocated fixed removedAddress :=
    allocated_of_bump_eq hremovedMoved hfixed.2.1
  have hremovedRoot : allocated rootBlackState removedAddress :=
    allocated_of_bump_eq hremovedFixed (paintNode_bumpIndex fixed fixed.root 0)
  have hsizeRoot : rootBlackState.size = s.size := by
    calc
      rootBlackState.size = fixed.size := paintNode_size fixed fixed.root 0
      _ = moved.size := hfixed.2.2
      _ = s.size := hmoved.2.2
  have hsizeRoot0 : (0 : Nat) < rootBlackState.size.toNat := by
    rw [hsizeRoot]
    exact hsz0
  exact releaseRemoved_delete_wf rootBlackState removedAddress hgRoot.1 hremovedRoot hsizeRoot0

/-- `releaseRemoved` 保持 `wf`（回收地址已分配且 size > 0）。 -/
private theorem releaseRemoved_wf (s : State) (addr : UInt64)
    (hwf : wf s) (ha : 1 ≤ addr ∧ addr < s.bumpIndex)
    (hsz0 : (0 : Nat) < s.size.toNat) : wf (releaseRemoved s addr) := by
  unfold releaseRemoved
  obtain ⟨hsz, hb1, hb5, hf5, hfb, hptr⟩ := hwf
  have ha0n : (1 : Nat) ≤ addr.toNat := ha.1
  have ha1n : addr.toNat < s.bumpIndex.toNat := ha.2
  have hb5n : s.bumpIndex.toNat ≤ 5 := hb5
  have haddr5 : addr.toNat ≤ 5 := by omega
  refine ⟨?_, hb1, hb5, ?_, ?_, ?_⟩
  · show (s.size - 1).toNat ≤ 4
    have hsz' : s.size.toNat ≤ 4 := hsz
    -- (size - 1).toNat ≤ size.toNat when size > 0
    have hsub : (s.size - 1).toNat ≤ s.size.toNat := by
      have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
      rw [UInt64.toNat_sub]
      -- size.toNat ≥ 1
      have : (1 : Nat) ≤ s.size.toNat := hsz0
      have hone : UInt64.toNat 1 = 1 := rfl
      simp only [hone, h2]
      have hszlt : s.size.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size _
      omega
    omega
  · show addr.toNat ≤ 5
    exact haddr5
  · show addr ≤ s.bumpIndex
    exact Nat.le_of_lt ha.2
  · intro a ha0 ha1
    have ha0n' : (1 : Nat) ≤ a.toNat := ha0
    have ha1n' : a.toNat < s.bumpIndex.toNat := ha1
    have hslot : (a.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hi4 : (addr.toNat - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hia : (addr.toNat - 1) % 4 = (a.toNat - 1) % 4
    · have hold := hptr a ha0 ha1
      have hget : (s.nodes.set ((addr.toNat - 1) % 4)
          { s.nodes[(addr.toNat - 1) % 4]! with
            left := s.freeHead, right := 0, parent := 0, color := 0 } hi4)[(a.toNat - 1) % 4]! =
          { s.nodes[(addr.toNat - 1) % 4]! with
            left := s.freeHead, right := 0, parent := 0, color := 0 } := by
        rw [← hia, vec_set_self]
      rw [hget]
      exact ⟨hfb, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    · have hget := vec_set_ne s.nodes ((addr.toNat - 1) % 4) ((a.toNat - 1) % 4)
        { s.nodes[(addr.toNat - 1) % 4]! with
          left := s.freeHead, right := 0, parent := 0, color := 0 } hi4 hia hslot
      rw [hget]
      exact hptr a ha0 ha1

/-- `removeNode` 成功时，在返回地址确属已分配节点且输入 size 非零的有效树上保持 `wf`。 -/
theorem removeNode_wf (s : State) (k : UInt64) {t : State} {a : UInt64}
    (h : removeNode s k = .ok (t, a))
    (hwf : wf s) (hlinks : linksAllocated s)
    (ha : allocated s a) (hsize : (0 : Nat) < s.size.toNat) :
    wf t := by
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
    if removedColor = 0 then
      fixDeleted moved replacementAddress replacementParent
    else moved
  let rootBlackState := paintNode fixed fixed.root 0
  let released := releaseRemoved rootBlackState removedAddress
  change
    (if removedAddress = 0 then
       (Except.error .overflow : Except Error (State × UInt64))
     else Except.ok (released, removedAddress)) = Except.ok (t, a) at h
  by_cases hremoved0 : removedAddress = 0
  · simp [hremoved0] at h
  · rw [if_neg hremoved0] at h
    injection h with hpair
    injection hpair with ht haeq
    subst t
    subst a
    have hremoved : allocated s removedAddress := ha
    have hg : deleteGeom s := ⟨hwf, hlinks⟩
    have hr := treeNode_deleteGeom s removedAddress removedAddress hg hremoved
      (Or.inr hremoved)
    change linkAllocated s removed.left ∧ linkAllocated s removed.right ∧
      linkAllocated s removed.parent ∧ removed.color ≤ 1 at hr
    have hsuccessor : allocated s successorAddress := by
      by_cases hleft0 : removed.left = 0
      · simpa [successorAddress, hleft0] using hremoved
      · by_cases hright0 : removed.right = 0
        · simpa [successorAddress, hleft0, hright0] using hremoved
        · have hroot : allocated s successorRoot := by
            exact hr.2.1.resolve_left hright0
          have hrootNode :=
            treeNode_deleteGeom s successorRoot removedAddress hg hremoved (Or.inr hroot)
          have hleft1 : linkAllocated s successorLeft1 := by
            simpa only [successorLeft1, successorRoot, removed, removedIndex, treeNode]
              using hrootNode.1
          have hleft2 : linkAllocated s successorLeft2 := by
            by_cases hleft10 : successorLeft1 = 0
            · exact Or.inl (by simp [successorLeft2, hleft10])
            · have hleft1Alloc : allocated s successorLeft1 :=
                hleft1.resolve_left hleft10
              have hleft1Node :=
                treeNode_deleteGeom s successorLeft1 removedAddress hg hremoved
                  (Or.inr hleft1Alloc)
              simpa [successorLeft2, hleft10, treeNode] using hleft1Node.1
          by_cases hleft20 : successorLeft2 = 0
          · by_cases hleft10 : successorLeft1 = 0
            · simpa [successorAddress, hleft0, hright0, hleft20, hleft10]
                using hroot
            · have hleft1Alloc : allocated s successorLeft1 :=
                hleft1.resolve_left hleft10
              simpa [successorAddress, hleft0, hright0, hleft20, hleft10]
                using hleft1Alloc
          · have hleft2Alloc : allocated s successorLeft2 :=
              hleft2.resolve_left hleft20
            simpa [successorAddress, hleft0, hright0, hleft20] using hleft2Alloc
    have hs := treeNode_deleteGeom s successorAddress removedAddress hg hremoved
      (Or.inr hsuccessor)
    change linkAllocated s successor.left ∧ linkAllocated s successor.right ∧
      linkAllocated s successor.parent ∧ successor.color ≤ 1 at hs
    have hreplacement : linkAllocated s replacementAddress := by
      by_cases hleft0 : successor.left = 0
      · simpa [replacementAddress, hleft0] using hs.2.1
      · simpa [replacementAddress, hleft0] using hs.1
    have hreplacementParent : linkAllocated s replacementParent := by
      by_cases hsame : successorAddress = removedAddress
      · simpa [replacementParent, hsame] using hr.2.2.1
      · by_cases hparent : successor.parent = removedAddress
        · have hrep : replacementParent = successorAddress := by
            simp [replacementParent, hsame, hparent]
          rw [hrep]
          change successorAddress = 0 ∨ allocated s successorAddress
          exact Or.inr hsuccessor
        · simpa [replacementParent, hsame, hparent] using hs.2.2.1
    have hpipeline :=
      removePipeline_wf s removedAddress successorAddress replacementAddress
        replacementParent removedColor hg hremoved hsuccessor hreplacement
        hreplacementParent hsize
    simpa [removed, removedIndex, treeNode, moved, fixed, rootBlackState, released]
      using hpipeline

end Proofs

end Examples.Svm.Tree