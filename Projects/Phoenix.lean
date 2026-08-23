import ProofForge

/-!
Phoenix v1 `src/state` 在本仓剖面下的摊平。

官方 `FIFOMarket` 是三棵红黑树 + 泛型 trader key。抽出器不认不定长树，
所以这里把官方 *记录* 摊成平行 `UInt64` 向量，并把 ask 树保存成其中序投影：

  FIFOOrderId          → priceTicks / sequences
  FIFORestingOrder     → traders / sizes / lastSlots / lastTimes
  TraderState          → quoteLocked / quoteFree / baseLocked / baseFree
  MatchingEngineResponse → match*（bounded fold scratch）
  OrderPacket.client_order_id u128、动态树分配器、MarketEvent 仍关

N=4。档 0 是最优 ask；同价时 sequence 小的在前。没有 bid 书。
`RBTree4` 给出这四档对应的红黑树拓扑见证；撮合只依赖中序次序，
不把颜色和指针复制进链上状态。
-/
namespace Projects.Phoenix

open ProofForge.Runtime

/-- 官方 `Side`。本切片只做 Ask。 -/
inductive Side where
  | bid
  | ask
  deriving Repr, DecidableEq, Inhabited, BEq

/-- 官方 `SelfTradeBehavior`。本切片不跑自成交。 -/
inductive SelfTradeBehavior where
  | abort
  | cancelProvide
  | decrementTake
  deriving Repr, DecidableEq, Inhabited, BEq

/--
摊平后的账户状态。字段名跟官方记录对齐，不是自己发明的 6 槽。

`_padding` 官方 32×u64，这里不存。
`collectedQuoteLotFees` / `unclaimedQuoteLotFees` 官方是 QuoteLots。
TIF 哨兵：`lastSlots[i] = 0` / `lastTimes[i] = 0` 表示不过期。
-/
structure State where
  baseLotsPerBaseUnit : UInt64
  tickSize : UInt64
  sequence : UInt64
  takerFeeBps : UInt64
  collectedFees : UInt64
  unclaimedFees : UInt64
  priceTicks : Vector UInt64 4
  sequences : Vector UInt64 4
  traders : Vector UInt64 4
  sizes : Vector UInt64 4
  lastSlots : Vector UInt64 4
  lastTimes : Vector UInt64 4
  quoteLocked : UInt64
  quoteFree : UInt64
  baseLocked : UInt64
  baseFree : UInt64
  /-- 最近一次 IOC 的瞬时响应；入口开始时清零，循环体用作有界 fold accumulator。 -/
  matchFilled : UInt64
  matchQuote : UInt64
  matchExpired : UInt64
  matchStopped : UInt64
  matchError : UInt64
  matchLevel : UInt64
  matchWant : UInt64
  matchLimit : UInt64
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

def empty4 : Vector UInt64 4 := #v[0, 0, 0, 0]

/-- 固定容量 ask 树的节点地址；0 是 Phoenix 的 sentinel。 -/
structure RBNode where
  left : UInt64
  right : UInt64
  parent : UInt64
  red : Bool
  level : UInt64
  deriving Repr, DecidableEq, Inhabited

structure RBTree4 where
  root : UInt64
  nodes : Vector RBNode 4
  deriving Repr, DecidableEq, Inhabited

/--
四个中序档的规范红黑拓扑。地址 2 是黑根；地址 4 是红叶。
每条 sentinel 路径的 black height 相同，且红节点没有红孩子。
-/
def canonicalAskTree : RBTree4 :=
  { root := 2
    nodes := #v[
      { left := 0, right := 0, parent := 2, red := false, level := 0 },
      { left := 1, right := 3, parent := 0, red := false, level := 1 },
      { left := 0, right := 4, parent := 2, red := false, level := 2 },
      { left := 0, right := 0, parent := 3, red := true, level := 3 }
    ] }

/-- 固定拓扑的中序游标；撮合器按这个顺序访问摊平档。 -/
def RBTree4.inorderLevels (tree : RBTree4) : Vector UInt64 4 :=
  #v[tree.nodes[0]!.level, tree.nodes[1]!.level,
    tree.nodes[2]!.level, tree.nodes[3]!.level]

/-- 本模型使用的四节点红黑拓扑不变量。 -/
def RBTree4.valid (tree : RBTree4) : Bool :=
  tree.root = 2 &&
    tree.nodes[0]!.left = 0 && tree.nodes[0]!.right = 0 &&
    tree.nodes[0]!.parent = 2 && !tree.nodes[0]!.red &&
    tree.nodes[1]!.left = 1 && tree.nodes[1]!.right = 3 &&
    tree.nodes[1]!.parent = 0 && !tree.nodes[1]!.red &&
    tree.nodes[2]!.left = 0 && tree.nodes[2]!.right = 4 &&
    tree.nodes[2]!.parent = 2 &&
    !tree.nodes[2]!.red &&
    tree.nodes[3]!.parent = 3 && tree.nodes[3]!.red &&
    tree.nodes[3]!.left = 0 && tree.nodes[3]!.right = 0 &&
    tree.inorderLevels = #v[0, 1, 2, 3]

/-- 中序投影保持 Phoenix 的 price-time FIFO 顺序。空档不参与比较。 -/
def orderedAsks (s : State) : Bool :=
  let before (i j : Nat) : Bool :=
    s.sizes[i]! = 0 || s.sizes[j]! = 0 ||
      s.priceTicks[i]! < s.priceTicks[j]! ||
      (s.priceTicks[i]! = s.priceTicks[j]! && s.sequences[i]! ≤ s.sequences[j]!)
  before 0 1 && before 0 2 && before 0 3 &&
    before 1 2 && before 1 3 && before 2 3

/-- 官方 taker fee 默认常用 5 bps。 -/
def defaultFeeBps : UInt64 := 5

/-- 不做 `n + d - 1`，避免上取整本身溢出。`d = 0` fail-closed 为 0。 -/
def ceilDiv (n d : UInt64) : UInt64 :=
  if d = 0 then 0
  else
    let q := n / d
    if n % d = 0 then q else q + 1

/--
UInt64 剖面的 bps 上取整。官方用 u128；本模型要求乘积留在 UInt64。
撮合入口会在调用前检查这个条件。
-/
def feeOfBps (qty feeBps : UInt64) : UInt64 :=
  ceilDiv (qty * feeBps) 10000

def feeOf (qty : UInt64) : UInt64 :=
  feeOfBps qty defaultFeeBps

@[pf_entry]
def init (tick : UInt64) : State :=
  { baseLotsPerBaseUnit := 1
    tickSize := tick
    sequence := 1
    takerFeeBps := defaultFeeBps
    collectedFees := 0
    unclaimedFees := 0
    priceTicks := empty4
    sequences := empty4
    traders := empty4
    sizes := empty4
    lastSlots := empty4
    lastTimes := empty4
    quoteLocked := 0
    quoteFree := 0
    baseLocked := 0
    baseFree := 0
    matchFilled := 0
    matchQuote := 0
    matchExpired := 0
    matchStopped := 0
    matchError := 0
    matchLevel := 0
    matchWant := 0
    matchLimit := 0 }

/-- 官方 FIFORestingOrder 是否过期。0 是哨兵。 -/
def expired (lastSlot lastTime nowSlot nowTime : UInt64) : Bool :=
  (lastSlot ≠ 0 && lastSlot < nowSlot) ||
    (lastTime ≠ 0 && lastTime < nowTime)

/-- 挂到第一档空位。链上只改 `sizes`；价/序号/锁仓是宿主语义。 -/
@[pf_entry]
def postAsk (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .ok ({ s with sizes := s.sizes.set 0 size }, size)
  else if s.sizes[1]! = 0 then
    .ok ({ s with sizes := s.sizes.set 1 size }, size)
  else if s.sizes[2]! = 0 then
    .ok ({ s with sizes := s.sizes.set 2 size }, size)
  else if s.sizes[3]! = 0 then
    .ok ({ s with sizes := s.sizes.set 3 size }, size)
  else
    .error .overflow

/-- 宿主：写 FIFOOrderId + 锁 base。抽出一次改多叶还不行。 -/
def postAskFull (s : State) (price size : UInt64) : Except Error (State × UInt64) :=
  match postAsk s size with
  | .error e => .error e
  | .ok (st, ret) =>
    if st.baseLocked ≤ u64Max - size then
      if st.sizes[0]! = size && s.sizes[0]! = 0 then
        .ok ({ st with
                priceTicks := st.priceTicks.set 0 price
                sequences := st.sequences.set 0 st.sequence
                sequence := st.sequence + 1
                baseLocked := st.baseLocked + size }, ret)
      else if st.sizes[1]! = size && s.sizes[1]! = 0 then
        .ok ({ st with
                priceTicks := st.priceTicks.set 1 price
                sequences := st.sequences.set 1 st.sequence
                sequence := st.sequence + 1
                baseLocked := st.baseLocked + size }, ret)
      else if st.sizes[2]! = size && s.sizes[2]! = 0 then
        .ok ({ st with
                priceTicks := st.priceTicks.set 2 price
                sequences := st.sequences.set 2 st.sequence
                sequence := st.sequence + 1
                baseLocked := st.baseLocked + size }, ret)
      else
        .ok ({ st with
                priceTicks := st.priceTicks.set 3 price
                sequences := st.sequences.set 3 st.sequence
                sequence := st.sequence + 1
                baseLocked := st.baseLocked + size }, ret)
    else
      .error .overflow

/-- 扫书期间的瞬时 `MatchingEngineResponse`。不进入账户 schema。 -/
structure MatchAcc where
  sizes : Vector UInt64 4
  filledBase : UInt64
  adjustedQuote : UInt64
  expiredBase : UInt64
  stopped : Bool
  deriving Repr, DecidableEq

/--
沿 ask 树中序投影做至多四档的 IOC。过期单取消并继续；第一档超限即停止；
整档成交继续，部分成交终止。所有乘加都在 UInt64 剖面内 fail-closed。
-/
private def scanAsks (s : State) (want limit nowSlot nowTime : UInt64)
    (fuel i : Nat) (acc : MatchAcc) : Except Error MatchAcc :=
  match fuel with
  | 0 => .ok acc
  | fuel' + 1 =>
    if acc.stopped || acc.filledBase = want then
      .ok acc
    else if h : i < 4 then
      let size := acc.sizes[i]
      if size = 0 then
        scanAsks s want limit nowSlot nowTime fuel' (i + 1) acc
      else if expired s.lastSlots[i] s.lastTimes[i] nowSlot nowTime then
        if acc.expiredBase ≤ u64Max - size then
          scanAsks s want limit nowSlot nowTime fuel' (i + 1)
            { acc with
              sizes := acc.sizes.set i 0
              expiredBase := acc.expiredBase + size }
        else
          .error .overflow
      else if limit < s.priceTicks[i] then
        .ok { acc with stopped := true }
      else
        let remaining := want - acc.filledBase
        let fill := if remaining ≤ size then remaining else size
        let price := s.priceTicks[i]
        if price = 0 || s.tickSize ≤ u64Max / price then
          let quotePerBase := price * s.tickSize
          if quotePerBase = 0 || fill ≤ u64Max / quotePerBase then
            let quote := quotePerBase * fill
            if acc.adjustedQuote ≤ u64Max - quote then
              scanAsks s want limit nowSlot nowTime fuel' (i + 1)
                { sizes := acc.sizes.set i (size - fill)
                  filledBase := acc.filledBase + fill
                  adjustedQuote := acc.adjustedQuote + quote
                  expiredBase := acc.expiredBase
                  stopped := fill = remaining }
            else
              .error .overflow
          else
            .error .overflow
        else
          .error .overflow
    else
      .ok acc

/--
把聚合撮合结果结算到摊平 TraderState。

本 N=4 模型把四个 maker 和一个 taker 聚合在一个账户里：`quoteLocked` 是
taker 预算，`quoteFree` 是 maker 收益，`baseLocked` 是 maker 锁仓，
`baseFree` 同时承载 taker 输出和过期单解锁。撮合只增加
`unclaimedFees`；`collectedFees` 留给独立收取动作。
-/
private def settleBuy (s : State) (acc : MatchAcc) : Except Error (State × UInt64) :=
  if s.baseLotsPerBaseUnit = 0 then
    .error .overflow
  else if acc.adjustedQuote ≠ 0 && s.takerFeeBps > u64Max / acc.adjustedQuote then
    .error .overflow
  else
    let quoteLots := ceilDiv acc.adjustedQuote s.baseLotsPerBaseUnit
    let adjustedFee := ceilDiv (acc.adjustedQuote * s.takerFeeBps) 10000
    let feeLots := ceilDiv adjustedFee s.baseLotsPerBaseUnit
    if quoteLots > u64Max - feeLots then
      .error .overflow
    else
      let quoteDebit := quoteLots + feeLots
      if quoteDebit > s.quoteLocked then
        .error .overflow
      else if acc.filledBase > u64Max - acc.expiredBase then
        .error .overflow
      else
        let makerBaseDebit := acc.filledBase + acc.expiredBase
        if makerBaseDebit > s.baseLocked then
          .error .overflow
        else
          let baseCredit := acc.filledBase + acc.expiredBase
          if s.baseFree > u64Max - baseCredit then
            .error .overflow
          else if s.quoteFree > u64Max - quoteLots then
            .error .overflow
          else if s.unclaimedFees > u64Max - feeLots then
            .error .overflow
          else
            let _ :=
              if acc.filledBase = 0 then 0
              else tokenTransferChecked acc.filledBase 6
            .ok ({ s with
                    sizes := acc.sizes
                    quoteLocked := s.quoteLocked - quoteDebit
                    quoteFree := s.quoteFree + quoteLots
                    baseLocked := s.baseLocked - makerBaseDebit
                    baseFree := s.baseFree + baseCredit
                    unclaimedFees := s.unclaimedFees + feeLots }, acc.filledBase)

/--
可测试的完整 N=4 IOC：红黑树中序跨档、严格 slot/time TIF、聚合费用和余额记账。
无流动性或首个有效价格超限是成功的零成交 IOC，不伪装成 overflow。
-/
def swapBuyAt (s : State) (want limit nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) := do
  let acc ← scanAsks s want limit nowSlot nowTime 4 0
    { sizes := s.sizes, filledBase := 0, adjustedQuote := 0,
      expiredBase := 0, stopped := false }
  settleBuy s acc

private def finishFold (s : State) (quoteLots feeLots : UInt64) :
    Except Error (State × UInt64) :=
  if quoteLots ≤ u64Max - feeLots then
    let quoteDebit := quoteLots + feeLots
    if quoteDebit ≤ s.quoteLocked then
      if s.matchFilled ≤ u64Max - s.matchExpired then
        let baseDebit := s.matchFilled + s.matchExpired
        if baseDebit ≤ s.baseLocked then
          if s.baseFree ≤ u64Max - baseDebit then
            if s.quoteFree ≤ u64Max - quoteLots then
              if s.unclaimedFees ≤ u64Max - feeLots then
                if s.matchFilled = 0 then
                  .ok ({ s with
                          quoteLocked := s.quoteLocked - quoteDebit
                          quoteFree := s.quoteFree + quoteLots
                          baseLocked := s.baseLocked - baseDebit
                          baseFree := s.baseFree + baseDebit
                          unclaimedFees := s.unclaimedFees + feeLots }, s.matchFilled)
                else
                  let _ := tokenTransferChecked s.matchFilled 6
                  .ok ({ s with
                          quoteLocked := s.quoteLocked - quoteDebit
                          quoteFree := s.quoteFree + quoteLots
                          baseLocked := s.baseLocked - baseDebit
                          baseFree := s.baseFree + baseDebit
                          unclaimedFees := s.unclaimedFees + feeLots }, s.matchFilled)
              else .error .overflow
            else .error .overflow
          else .error .overflow
        else .error .overflow
      else .error .overflow
    else .error .overflow
  else .error .overflow

private def settleFold (s : State) : Except Error (State × UInt64) :=
  if s.matchError ≠ 0 then .error .overflow
  else if s.baseLotsPerBaseUnit = 0 then .error .overflow
  else if s.matchQuote = 0 then finishFold s 0 0
  else
    let quoteLots := (s.matchQuote - 1) / s.baseLotsPerBaseUnit + 1
    if s.takerFeeBps = 0 then
      finishFold s quoteLots 0
    else if s.takerFeeBps ≤ u64Max / s.matchQuote then
      let feeProduct := s.matchQuote * s.takerFeeBps
      let adjustedFee := (feeProduct - 1) / 10000 + 1
      let feeLots := (adjustedFee - 1) / s.baseLotsPerBaseUnit + 1
      finishFold s quoteLots feeLots
    else .error .overflow

attribute [pf_inline] finishFold settleFold

/--
链上 N=4 IOC。十七次 state-carrying bounded fold：第 0 次清瞬时响应，
其余十六次按四档 ×（slot TIF、time TIF、撮合、advance）推进。把每档拆成显式
phase，避免 Lean 的可变 `do` 把公共 continuation 复制进每个分支；循环 store
会继续下一次，不再静态复制后续档位。
-/
@[pf_entry]
def swapBuy (s : State) (want limit : UInt64) : Except Error (State × UInt64) := Id.run do
  let mut st := s
  for i in [0:17] do
    if i = 0 then
      st := { st with
        matchFilled := 0, matchQuote := 0, matchExpired := 0,
        matchStopped := 0, matchError := 0, matchLevel := 0,
        matchWant := want, matchLimit := limit }
    else if st.matchStopped = 0 then
      let k := i - 1
      let phase := k % 4
      let j := st.matchLevel.toNat
      let size := st.sizes[j]!
      if st.matchFilled = st.matchWant then
        st := { st with matchStopped := 1 }
      else if phase = 3 then
        st := { st with matchLevel := st.matchLevel + 1 }
      else if size ≠ 0 then
        if phase = 0 then
          if st.lastSlots[j]! ≠ 0 then
            if st.lastSlots[j]! < clockSlot then
              if st.matchExpired ≤ u64Max - size then
                st := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchExpired := st.matchExpired + size }
              else
                st := { st with matchStopped := 1, matchError := 1 }
        else if phase = 1 then
          if st.lastTimes[j]! ≠ 0 then
            if st.lastTimes[j]! < unixTime then
              if st.matchExpired ≤ u64Max - size then
                st := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchExpired := st.matchExpired + size }
              else
                st := { st with matchStopped := 1, matchError := 1 }
        else if phase = 2 then
          if st.matchLimit < st.priceTicks[j]! then
            st := { st with matchStopped := 1 }
          else
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let fill := remaining
              let price := st.priceTicks[j]!
              if price = 0 then
                st := { st with
                  sizes := st.sizes.set (j % 4) (size - fill)
                  matchFilled := st.matchFilled + fill
                  matchStopped := 1 }
              else if st.tickSize ≤ u64Max / price then
                let quotePerBase := price * st.tickSize
                if quotePerBase = 0 then
                  st := { st with
                    sizes := st.sizes.set (j % 4) (size - fill)
                    matchFilled := st.matchFilled + fill
                    matchStopped := 1 }
                else if fill ≤ u64Max / quotePerBase then
                  let quote := quotePerBase * fill
                  if st.matchQuote ≤ u64Max - quote then
                    st := { st with
                      sizes := st.sizes.set (j % 4) (size - fill)
                      matchFilled := st.matchFilled + fill
                      matchQuote := st.matchQuote + quote
                      matchStopped := 1 }
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
                else
                  st := { st with matchStopped := 1, matchError := 1 }
              else
                st := { st with matchStopped := 1, matchError := 1 }
            else
              let fill := size
              let price := st.priceTicks[j]!
              if price = 0 then
                st := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchFilled := st.matchFilled + fill }
              else if st.tickSize ≤ u64Max / price then
                let quotePerBase := price * st.tickSize
                if quotePerBase = 0 then
                  st := { st with
                    sizes := st.sizes.set (j % 4) 0
                    matchFilled := st.matchFilled + fill }
                else if fill ≤ u64Max / quotePerBase then
                  let quote := quotePerBase * fill
                  if st.matchQuote ≤ u64Max - quote then
                    st := { st with
                      sizes := st.sizes.set (j % 4) 0
                      matchFilled := st.matchFilled + fill
                      matchQuote := st.matchQuote + quote }
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
                else
                  st := { st with matchStopped := 1, matchError := 1 }
              else
                st := { st with matchStopped := 1, matchError := 1 }
  settleFold st

/-- 官方 ReduceOrder：减档 0。锁仓调整在宿主。 -/
@[pf_entry]
def reduceAsk (s : State) (qty : UInt64) : Except Error (State × UInt64) :=
  if qty ≤ s.sizes[0]! then
    .ok ({ s with sizes := s.sizes.set 0 (s.sizes[0]! - qty) }, qty)
  else
    .error .overflow

/-- 官方部分成交：吃光档 0。抽出还认不了 `set 0 0`。 -/
def sweepAsk (s : State) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .error .overflow
  else if s.baseFree ≤ u64Max - s.sizes[0]! then
    if s.sizes[0]! ≤ s.baseLocked then
      let _ := tokenTransferChecked s.sizes[0]! 6
      .ok ({ s with
              sizes := s.sizes.set 0 (s.sizes[0]! - s.sizes[0]!)
              baseLocked := s.baseLocked - s.sizes[0]!
              baseFree := s.baseFree + s.sizes[0]! }, s.sizes[0]!)
    else
      .error .overflow
  else
    .error .overflow

/-- 官方 CancelOrder。抽出还认不了 `size - size`。 -/
def cancelAsk (s : State) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .error .overflow
  else if s.sizes[0]! ≤ s.baseLocked then
    .ok ({ s with
            sizes := s.sizes.set 0 (s.sizes[0]! - s.sizes[0]!)
            baseLocked := s.baseLocked - s.sizes[0]! }, s.sizes[0]!)
  else
    .error .overflow

def takeFee (qty : UInt64) : UInt64 :=
  if qty = 0 then 0 else feeOf qty

def checkLimit (s : State) (limit : UInt64) : Bool :=
  limit ≥ s.priceTicks[0]!

def checkTif (deadline : UInt64) : Bool :=
  deadline = 0 || unixTime < deadline

@[pf_entry]
def bestAsk (s : State) : UInt64 :=
  s.priceTicks[0]!

@[pf_entry]
def askQty (s : State) : UInt64 :=
  s.sizes[0]! + s.sizes[1]! + s.sizes[2]! + s.sizes[3]!

@[pf_entry]
def makerBase (s : State) : UInt64 :=
  s.baseLocked

@[pf_entry]
def takerBase (s : State) : UInt64 :=
  s.baseFree

@[pf_entry]
def nextSeq (s : State) : UInt64 :=
  s.sequence

@[pf_entry]
def feeBpsOf (s : State) : UInt64 :=
  s.takerFeeBps

@[pf_entry]
def level0 (s : State) : UInt64 :=
  s.sizes[0]!

end Projects.Phoenix
