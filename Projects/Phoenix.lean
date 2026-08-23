import ProofForge

/-!
Phoenix v1 `src/state` 在本仓剖面下的摊平。

官方 `FIFOMarket` 是三棵红黑树 + 泛型 trader key。抽出器不认不定长树，
所以这里把官方 *记录* 摊成平行 `UInt64` 向量，并把双边书保存成各自最优优先投影：

  FIFOOrderId          → priceTicks / sequences
  FIFORestingOrder     → traders / sizes / lastSlots / lastTimes
  TraderState          → traderQuoteLocked / traderQuoteFree / traderBaseLocked / traderBaseFree
  MatchingEngineResponse → match*（bounded fold scratch）
  MarketEvent          → events（固定容量 batch）+ lastEvent（兼容投影）
  OrderPacket.client_order_id → little-endian UInt64 × UInt64
  traders tree         → 4×Pubkey limbs + allocator metadata + per-seat TraderState

每边 N=4。档 0 是最优价；ask 价格升序、bid 价格降序，同价均为 FIFO。
`RBTree4` 给出四档对应的红黑树拓扑见证；撮合只依赖中序次序，
不把颜色和指针复制进链上状态。free-funds 挂单、驱逐、按 ID reduce/cancel、
三种 self-trade 和 fee collection 已进入 bounded 模型。trader registry 保留
Sokoban 的 1-based address、bump 分配与 LIFO free-list；withdraw 和 zero-state
seat eviction 已接入，订单仍只存内部 address。
-/
namespace Projects.Phoenix

open ProofForge.Svm.Runtime

/-- 官方 `Side`。 -/
inductive Side where
  | bid
  | ask
  deriving Repr, DecidableEq, Inhabited, BEq

/-- 官方 `SelfTradeBehavior`；链上 ABI 用 0/1/2 编码。 -/
inductive SelfTradeBehavior where
  | abort
  | cancelProvide
  | decrementTake
  deriving Repr, DecidableEq, Inhabited, BEq

/--
官方内部 `MarketEvent` 的 bounded 形状。maker 暂存 trader tree 的内部 address；
client id 已是 u128 的两个 little-endian limbs。把 maker address resolve 为 Pubkey，
以及 Borsh event batch，属于后续 wire/event-recorder adapter。
-/
inductive MarketEvent where
  | uninitialized
  | fill (maker orderSequence price filled remaining : UInt64)
  /-- `clientOrderIdLo` then `clientOrderIdHi` is the little-endian two-limb form of Phoenix's u128. -/
  | place (orderSequence clientOrderIdLo clientOrderIdHi price placed : UInt64)
  | reduce (orderSequence price removed remaining : UInt64)
  | evict (maker orderSequence price evicted : UInt64)
  | fillSummary (clientOrderIdLo clientOrderIdHi totalBase totalQuote totalFee : UInt64)
  | fee (feesCollected : UInt64)
  | timeInForce (orderSequence lastValidSlot lastValidTime : UInt64)
  | expiredOrder (maker orderSequence price removed : UInt64)
  deriving Repr, DecidableEq, Inhabited

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
  bidPriceTicks : Vector UInt64 4
  bidSequences : Vector UInt64 4
  bidTraders : Vector UInt64 4
  bidSizes : Vector UInt64 4
  bidLastSlots : Vector UInt64 4
  bidLastTimes : Vector UInt64 4
  /--
  官方 traders 红黑树的 bounded allocator。address 0 是 sentinel，1..4 是 seat；
  `traderFreeHead = traderBumpIndex` 表示从 bump 区分配，否则弹 LIFO free-list。
  -/
  traderCount : UInt64
  traderBumpIndex : UInt64
  traderFreeHead : UInt64
  traderNextFree : Vector UInt64 4
  traderUsed : Vector UInt64 4
  /-- Solana Pubkey 的四个 little-endian UInt64 limbs，按 seat 平行存放。 -/
  traderKey0 : Vector UInt64 4
  traderKey1 : Vector UInt64 4
  traderKey2 : Vector UInt64 4
  traderKey3 : Vector UInt64 4
  /-- 官方 `TraderState`；每个余额都按内部 seat address 索引。 -/
  traderQuoteLocked : Vector UInt64 4
  traderQuoteFree : Vector UInt64 4
  traderBaseLocked : Vector UInt64 4
  traderBaseFree : Vector UInt64 4
  /-- 旧撮合路径保留的 market-wide 兼容投影；接入 per-seat 结算后再删。 -/
  quoteLocked : UInt64
  quoteFree : UInt64
  baseLocked : UInt64
  baseFree : UInt64
  /-- 最近一次 IOC 的瞬时响应；入口开始时清零，循环体用作有界 fold accumulator。 -/
  matchFilled : UInt64
  matchQuote : UInt64
  matchMakerQuote : UInt64
  matchExpired : UInt64
  matchStopped : UInt64
  matchError : UInt64
  matchLevel : UInt64
  matchWant : UInt64
  matchLimit : UInt64
  /-- 当前 instruction 的 fixed-capacity event batch；`eventCount` 之前的元素有效。 -/
  events : Vector MarketEvent 5
  eventCount : UInt64
  /-- 最近一个 bounded market event，保留为事件 batch 的兼容投影。 -/
  lastEvent : MarketEvent
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

def empty4 : Vector UInt64 4 := #v[0, 0, 0, 0]

def emptyEvents : Vector MarketEvent 5 :=
  #v[.uninitialized, .uninitialized, .uninitialized, .uninitialized, .uninitialized]

/-- 每个 instruction 覆盖上一批事件；旧 payload 无需清零，`eventCount` 决定有效前缀。 -/
private def beginEvents (s : State) : State :=
  { s with eventCount := 0, lastEvent := .uninitialized }

/-- 写满后 fail-closed 地丢弃额外事件；N=4 撮合至多四个逐档事件加一个 summary。 -/
private def appendEvent (s : State) (event : MarketEvent) : State :=
  if h : s.eventCount.toNat < 5 then
    { s with
      events := s.events.set s.eventCount.toNat event
      eventCount := s.eventCount + 1
      lastEvent := event }
  else
    s

attribute [pf_inline] beginEvents appendEvent

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

/-- bid 投影按价格降序、同价 encoded sequence 降序；`~~~sequence` 保持 FIFO。 -/
def orderedBids (s : State) : Bool :=
  let before (i j : Nat) : Bool :=
    s.bidSizes[i]! = 0 || s.bidSizes[j]! = 0 ||
      s.bidPriceTicks[j]! < s.bidPriceTicks[i]! ||
      (s.bidPriceTicks[i]! = s.bidPriceTicks[j]! &&
        s.bidSequences[j]! ≤ s.bidSequences[i]!)
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
    bidPriceTicks := empty4
    bidSequences := empty4
    bidTraders := empty4
    bidSizes := empty4
    bidLastSlots := empty4
    bidLastTimes := empty4
    traderCount := 0
    traderBumpIndex := 1
    traderFreeHead := 1
    traderNextFree := empty4
    traderUsed := empty4
    traderKey0 := empty4
    traderKey1 := empty4
    traderKey2 := empty4
    traderKey3 := empty4
    traderQuoteLocked := empty4
    traderQuoteFree := empty4
    traderBaseLocked := empty4
    traderBaseFree := empty4
    quoteLocked := 0
    quoteFree := 0
    baseLocked := 0
    baseFree := 0
    matchFilled := 0
    matchQuote := 0
    matchMakerQuote := 0
    matchExpired := 0
    matchStopped := 0
    matchError := 0
    matchLevel := 0
    matchWant := 0
    matchLimit := 0
    events := emptyEvents
    eventCount := 0
    lastEvent := .uninitialized }

/-- 完整四 limb Pubkey lookup；`traderUsed` 单独区分合法的全零 Pubkey 与空 seat。 -/
private def traderAddressFor (s : State) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  if s.traderUsed[0]! ≠ 0 && s.traderKey0[0]! = key0 && s.traderKey1[0]! = key1 &&
      s.traderKey2[0]! = key2 && s.traderKey3[0]! = key3 then 1
  else if s.traderUsed[1]! ≠ 0 && s.traderKey0[1]! = key0 && s.traderKey1[1]! = key1 &&
      s.traderKey2[1]! = key2 && s.traderKey3[1]! = key3 then 2
  else if s.traderUsed[2]! ≠ 0 && s.traderKey0[2]! = key0 && s.traderKey1[2]! = key1 &&
      s.traderKey2[2]! = key2 && s.traderKey3[2]! = key3 then 3
  else if s.traderUsed[3]! ≠ 0 && s.traderKey0[3]! = key0 && s.traderKey1[3]! = key1 &&
      s.traderKey2[3]! = key2 && s.traderKey3[3]! = key3 then 4
  else 0

attribute [pf_inline] traderAddressFor

/-- Stateful callers use an `Except` producer so the bounded lookup joins into a CFG local. -/
private def requireTraderAddress (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error UInt64 :=
  if s.traderUsed[0]! ≠ 0 && s.traderKey0[0]! = key0 && s.traderKey1[0]! = key1 &&
      s.traderKey2[0]! = key2 && s.traderKey3[0]! = key3 then .ok 1
  else if s.traderUsed[1]! ≠ 0 && s.traderKey0[1]! = key0 && s.traderKey1[1]! = key1 &&
      s.traderKey2[1]! = key2 && s.traderKey3[1]! = key3 then .ok 2
  else if s.traderUsed[2]! ≠ 0 && s.traderKey0[2]! = key0 && s.traderKey1[2]! = key1 &&
      s.traderKey2[2]! = key2 && s.traderKey3[2]! = key3 then .ok 3
  else if s.traderUsed[3]! ≠ 0 && s.traderKey0[3]! = key0 && s.traderKey1[3]! = key1 &&
      s.traderKey2[3]! = key2 && s.traderKey3[3]! = key3 then .ok 4
  else .error .overflow

attribute [pf_inline] requireTraderAddress

/-- Host/view lookup；返回官方 1-based trader index，0 表示未注册。 -/
@[pf_entry]
def traderIndexOf (s : State) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  traderAddressFor s key0 key1 key2 key3

/-- 读取某 seat 的 base-free；无效或未分配 address fail-closed 为 0。 -/
@[pf_entry]
def traderBaseFreeAt (s : State) (address : UInt64) : UInt64 :=
  if address = 0 || 4 < address then 0
  else
    let i := address.toNat - 1
    if s.traderUsed[i]! = 0 then 0 else s.traderBaseFree[i]!

/--
官方 deposit 的 bounded state transition：先按完整 Pubkey 查 seat；缺失时走
Sokoban allocator 注册，再分别增加该 seat 的 base/quote free。重复注册幂等，
容量满和余额溢出都 fail closed。返回 1-based trader index。

循环中的 address 用字面量 select，而不是 `i + 1`：这样它保持 state-carrying
`forBody`，不会被纯加法的 `forAccum` 识别规则误收。
-/
def depositFundsFor (s : State) (key0 key1 key2 key3 baseLots quoteLots : UInt64) :
    Except Error (State × UInt64) := Id.run do
  let mut st := { s with matchStopped := 0 }
  for i in [0:4] do
    if st.matchStopped = (0 : UInt64) then
      let j : Nat := i
      if st.traderUsed[j]! ≠ (0 : UInt64) then
        if st.traderKey0[j]! = key0 then
          if st.traderKey1[j]! = key1 then
            if st.traderKey2[j]! = key2 then
              if st.traderKey3[j]! = key3 then
                let address : UInt64 :=
                  if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 4
                st := { st with matchStopped := address }
  if st.matchStopped ≠ (0 : UInt64) then
    let address := st.matchStopped
    let i := address.toNat - 1
    if h : i < 4 then
      if st.traderBaseFree[i]! ≤ u64Max - baseLots then
        if st.traderQuoteFree[i]! ≤ u64Max - quoteLots then
          .ok ({ st with
                  traderBaseFree := st.traderBaseFree.set i (st.traderBaseFree[i]! + baseLots)
                  traderQuoteFree :=
                    st.traderQuoteFree.set i (st.traderQuoteFree[i]! + quoteLots) },
            st.matchStopped)
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else if st.traderCount < (4 : UInt64) then
    if st.traderFreeHead = st.traderBumpIndex then
      if st.traderBumpIndex = (0 : UInt64) then
        .error .overflow
      else if st.traderBumpIndex < (5 : UInt64) then
        let address := st.traderBumpIndex
        let i := address.toNat - 1
        .ok ({ st with
                traderCount := st.traderCount + 1
                traderBumpIndex := st.traderBumpIndex + 1
                traderFreeHead := st.traderBumpIndex + 1
                traderNextFree := st.traderNextFree.set (i % 4) 0
                traderUsed := st.traderUsed.set (i % 4) 1
                traderKey0 := st.traderKey0.set (i % 4) key0
                traderKey1 := st.traderKey1.set (i % 4) key1
                traderKey2 := st.traderKey2.set (i % 4) key2
                traderKey3 := st.traderKey3.set (i % 4) key3
                traderQuoteLocked := st.traderQuoteLocked.set (i % 4) 0
                traderQuoteFree := st.traderQuoteFree.set (i % 4) quoteLots
                traderBaseLocked := st.traderBaseLocked.set (i % 4) 0
                traderBaseFree := st.traderBaseFree.set (i % 4) baseLots
                matchStopped := address }, address)
      else
        .error .overflow
    else if st.traderFreeHead = (0 : UInt64) then
      .error .overflow
    else if st.traderFreeHead < (5 : UInt64) then
      let address := st.traderFreeHead
      let i := address.toNat - 1
      let next := st.traderNextFree[i]!
      .ok ({ st with
              traderCount := st.traderCount + 1
              traderFreeHead := next
              traderNextFree := st.traderNextFree.set (i % 4) 0
              traderUsed := st.traderUsed.set (i % 4) 1
              traderKey0 := st.traderKey0.set (i % 4) key0
              traderKey1 := st.traderKey1.set (i % 4) key1
              traderKey2 := st.traderKey2.set (i % 4) key2
              traderKey3 := st.traderKey3.set (i % 4) key3
              traderQuoteLocked := st.traderQuoteLocked.set (i % 4) 0
              traderQuoteFree := st.traderQuoteFree.set (i % 4) quoteLots
              traderBaseLocked := st.traderBaseLocked.set (i % 4) 0
              traderBaseFree := st.traderBaseFree.set (i % 4) baseLots
              matchStopped := address }, address)
    else
      .error .overflow
  else
    .error .overflow

attribute [pf_inline] depositFundsFor

/--
SVM adapter：market 是 account 0，trader signer 是 account 1。`signerKey 1`
同时验证签名并返回 Pubkey 的第 0 limb；其余 limbs 走同一 account-header view。
-/
@[pf_entry]
def depositFunds (s : State) (baseLots quoteLots : UInt64) :
    Except Error (State × UInt64) :=
  depositFundsFor s (signerKey 1) (accKeyWord 1 1) (accKeyWord 1 2) (accKeyWord 1 3)
    baseLots quoteLots

/--
从一个已注册 seat 提取 base free funds。官方语义是 `min(requested, free)`；
返回实际可提取的 base lots，找不到完整 Pubkey 时 fail closed。
-/
def withdrawBaseFor (s : State) (key0 key1 key2 key3 requested : UInt64) :
    Except Error (State × UInt64) := do
  let address ← requireTraderAddress s key0 key1 key2 key3
  let i := address.toNat - 1
  let available := s.traderBaseFree[i]!
  let amount := if requested < available then requested else available
  .ok ({ s with
          traderBaseFree := s.traderBaseFree.set (i % 4) (available - amount) }, amount)

/-- Quote-lot 版本；单独入口避免把 base/quote 两种单位混进一个 UInt64 返回值。 -/
def withdrawQuoteFor (s : State) (key0 key1 key2 key3 requested : UInt64) :
    Except Error (State × UInt64) := do
  let address ← requireTraderAddress s key0 key1 key2 key3
  let i := address.toNat - 1
  let available := s.traderQuoteFree[i]!
  let amount := if requested < available then requested else available
  .ok ({ s with
          traderQuoteFree := s.traderQuoteFree.set (i % 4) (available - amount) }, amount)

/--
只有 `TraderState` 四类余额都为零时才释放 seat。释放后的 1-based address 压入
Sokoban LIFO free-list；bump index 不回退，下一次注册优先复用 free-list 头。
-/
def evictSeatFor (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) := do
  let address ← requireTraderAddress s key0 key1 key2 key3
  let i := address.toNat - 1
  if s.traderQuoteLocked[i]! = 0 && s.traderQuoteFree[i]! = 0 &&
      s.traderBaseLocked[i]! = 0 && s.traderBaseFree[i]! = 0 then
    if s.traderCount = 0 then
      .error .overflow
    else
      .ok ({ s with
              traderCount := s.traderCount - 1
              traderFreeHead := address
              traderNextFree := s.traderNextFree.set (i % 4) s.traderFreeHead
              traderUsed := s.traderUsed.set (i % 4) 0
              traderKey0 := s.traderKey0.set (i % 4) 0
              traderKey1 := s.traderKey1.set (i % 4) 0
              traderKey2 := s.traderKey2.set (i % 4) 0
              traderKey3 := s.traderKey3.set (i % 4) 0 }, address)
  else
    .error .overflow

attribute [pf_inline] withdrawBaseFor withdrawQuoteFor evictSeatFor

/-- SVM base-vault adapter；account 1 必须签名并以完整 Pubkey 拥有目标 seat。 -/
@[pf_entry]
def withdrawBase (s : State) (requested : UInt64) : Except Error (State × UInt64) :=
  withdrawBaseFor s (signerKey 1) (accKeyWord 1 1) (accKeyWord 1 2) (accKeyWord 1 3)
    requested

/-- SVM quote-vault adapter；返回实际提取的 quote lots。 -/
@[pf_entry]
def withdrawQuote (s : State) (requested : UInt64) : Except Error (State × UInt64) :=
  withdrawQuoteFor s (signerKey 1) (accKeyWord 1 1) (accKeyWord 1 2) (accKeyWord 1 3)
    requested

/-- SVM seat eviction adapter；非空 TraderState 或未注册 signer 都拒绝。 -/
@[pf_entry]
def evictSeat (s : State) : Except Error (State × UInt64) :=
  evictSeatFor s (signerKey 1) (accKeyWord 1 1) (accKeyWord 1 2) (accKeyWord 1 3)

/-- 官方 FIFORestingOrder 是否过期。0 是哨兵。 -/
def expired (lastSlot lastTime nowSlot nowTime : UInt64) : Bool :=
  (lastSlot ≠ 0 && lastSlot < nowSlot) ||
    (lastTime ≠ 0 && lastTime < nowTime)

/-- Phoenix 给自然 sequence 留半个 `u64` 空间；bid 用按位取反编码另一半。 -/
def maxOrderSequence : UInt64 := u64Max / 2

private def registeredSeat (s : State) (address : UInt64) : Bool :=
  if address = 0 || 4 < address then false
  else s.traderUsed[address.toNat - 1]! ≠ 0

/--
Apply the base-ledger part of posting an ask. `oldSize = 0` is an ordinary insertion;
otherwise the old maker is unlocked before the new owner is locked. Registered orders
update the authoritative per-seat ledger and the temporary aggregate projection atomically.
Unregistered addresses retain the host-reference aggregate path and are unreachable through
the authenticated instruction adapter.
-/
private def postAskFunds
    (s : State) (trader oldTrader oldSize size : UInt64) : State :=
  if oldSize > s.baseLocked then
    { s with matchError := 1 }
  else if s.baseFree > u64Max - oldSize then
    { s with matchError := 1 }
  else
    let aggregateFree := s.baseFree + oldSize
    let aggregateLocked := s.baseLocked - oldSize
    if size > aggregateFree then
      { s with matchError := 1 }
    else if aggregateLocked > u64Max - size then
      { s with matchError := 1 }
    else
      let aggregate := { s with
        baseLocked := aggregateLocked + size
        baseFree := aggregateFree - size }
      if registeredSeat s trader then
        let traderIndex := trader.toNat - 1
        if oldSize = 0 then
          if size > s.traderBaseFree[traderIndex]! then
            { s with matchError := 1 }
          else if s.traderBaseLocked[traderIndex]! > u64Max - size then
            { s with matchError := 1 }
          else
            { aggregate with
              traderBaseLocked := s.traderBaseLocked.set (traderIndex % 4)
                (s.traderBaseLocked[traderIndex]! + size)
              traderBaseFree := s.traderBaseFree.set (traderIndex % 4)
                (s.traderBaseFree[traderIndex]! - size) }
        else if registeredSeat s oldTrader then
          let oldIndex := oldTrader.toNat - 1
          if oldTrader = trader then
            if oldSize > s.traderBaseLocked[traderIndex]! then
              { s with matchError := 1 }
            else if s.traderBaseFree[traderIndex]! > u64Max - oldSize then
              { s with matchError := 1 }
            else
              let traderFree := s.traderBaseFree[traderIndex]! + oldSize
              let traderLocked := s.traderBaseLocked[traderIndex]! - oldSize
              if size > traderFree then
                { s with matchError := 1 }
              else if traderLocked > u64Max - size then
                { s with matchError := 1 }
              else
                { aggregate with
                  traderBaseLocked := s.traderBaseLocked.set (traderIndex % 4)
                    (traderLocked + size)
                  traderBaseFree := s.traderBaseFree.set (traderIndex % 4)
                    (traderFree - size) }
          else if oldSize > s.traderBaseLocked[oldIndex]! then
            { s with matchError := 1 }
          else if s.traderBaseFree[oldIndex]! > u64Max - oldSize then
            { s with matchError := 1 }
          else if size > s.traderBaseFree[traderIndex]! then
            { s with matchError := 1 }
          else if s.traderBaseLocked[traderIndex]! > u64Max - size then
            { s with matchError := 1 }
          else
            { aggregate with
              traderBaseLocked :=
                (s.traderBaseLocked.set (oldIndex % 4)
                  (s.traderBaseLocked[oldIndex]! - oldSize)).set (traderIndex % 4)
                    (s.traderBaseLocked[traderIndex]! + size)
              traderBaseFree :=
                (s.traderBaseFree.set (oldIndex % 4)
                  (s.traderBaseFree[oldIndex]! + oldSize)).set (traderIndex % 4)
                    (s.traderBaseFree[traderIndex]! - size) }
        else
          { s with matchError := 1 }
      else
        aggregate

/-- Quote-ledger analogue of `postAskFunds`; values are precomputed bid collateral. -/
private def postBidFunds
    (s : State) (trader oldTrader oldLock newLock : UInt64) : State :=
  if oldLock > s.quoteLocked then
    { s with matchError := 1 }
  else if s.quoteFree > u64Max - oldLock then
    { s with matchError := 1 }
  else
    let aggregateFree := s.quoteFree + oldLock
    let aggregateLocked := s.quoteLocked - oldLock
    if newLock > aggregateFree then
      { s with matchError := 1 }
    else if aggregateLocked > u64Max - newLock then
      { s with matchError := 1 }
    else
      let aggregate := { s with
        quoteLocked := aggregateLocked + newLock
        quoteFree := aggregateFree - newLock }
      if registeredSeat s trader then
        let traderIndex := trader.toNat - 1
        if oldLock = 0 then
          if newLock > s.traderQuoteFree[traderIndex]! then
            { s with matchError := 1 }
          else if s.traderQuoteLocked[traderIndex]! > u64Max - newLock then
            { s with matchError := 1 }
          else
            { aggregate with
              traderQuoteLocked := s.traderQuoteLocked.set (traderIndex % 4)
                (s.traderQuoteLocked[traderIndex]! + newLock)
              traderQuoteFree := s.traderQuoteFree.set (traderIndex % 4)
                (s.traderQuoteFree[traderIndex]! - newLock) }
        else if registeredSeat s oldTrader then
          let oldIndex := oldTrader.toNat - 1
          if oldTrader = trader then
            if oldLock > s.traderQuoteLocked[traderIndex]! then
              { s with matchError := 1 }
            else if s.traderQuoteFree[traderIndex]! > u64Max - oldLock then
              { s with matchError := 1 }
            else
              let traderFree := s.traderQuoteFree[traderIndex]! + oldLock
              let traderLocked := s.traderQuoteLocked[traderIndex]! - oldLock
              if newLock > traderFree then
                { s with matchError := 1 }
              else if traderLocked > u64Max - newLock then
                { s with matchError := 1 }
              else
                { aggregate with
                  traderQuoteLocked := s.traderQuoteLocked.set (traderIndex % 4)
                    (traderLocked + newLock)
                  traderQuoteFree := s.traderQuoteFree.set (traderIndex % 4)
                    (traderFree - newLock) }
          else if oldLock > s.traderQuoteLocked[oldIndex]! then
            { s with matchError := 1 }
          else if s.traderQuoteFree[oldIndex]! > u64Max - oldLock then
            { s with matchError := 1 }
          else if newLock > s.traderQuoteFree[traderIndex]! then
            { s with matchError := 1 }
          else if s.traderQuoteLocked[traderIndex]! > u64Max - newLock then
            { s with matchError := 1 }
          else
            { aggregate with
              traderQuoteLocked :=
                (s.traderQuoteLocked.set (oldIndex % 4)
                  (s.traderQuoteLocked[oldIndex]! - oldLock)).set (traderIndex % 4)
                    (s.traderQuoteLocked[traderIndex]! + newLock)
              traderQuoteFree :=
                (s.traderQuoteFree.set (oldIndex % 4)
                  (s.traderQuoteFree[oldIndex]! + oldLock)).set (traderIndex % 4)
                    (s.traderQuoteFree[traderIndex]! - newLock) }
        else
          { s with matchError := 1 }
      else
        aggregate

attribute [pf_inline] registeredSeat postAskFunds postBidFunds

private def swapAskAdjacent (s : State) (j : Nat) : State :=
  let r := j + 1
  { s with
    priceTicks :=
      (s.priceTicks.set (j % 4) s.priceTicks[r]!).set (r % 4) s.priceTicks[j]!
    sequences :=
      (s.sequences.set (j % 4) s.sequences[r]!).set (r % 4) s.sequences[j]!
    traders :=
      (s.traders.set (j % 4) s.traders[r]!).set (r % 4) s.traders[j]!
    sizes :=
      (s.sizes.set (j % 4) s.sizes[r]!).set (r % 4) s.sizes[j]!
    lastSlots :=
      (s.lastSlots.set (j % 4) s.lastSlots[r]!).set (r % 4) s.lastSlots[j]!
    lastTimes :=
      (s.lastTimes.set (j % 4) s.lastTimes[r]!).set (r % 4) s.lastTimes[j]! }

attribute [pf_inline] swapAskAdjacent

/--
固定容量有序投影的 ask 插入。阶段 0–3 找空槽，阶段 4 在满书时按
`get_max()` 语义驱逐最差订单，阶段 5–13 用相邻 compare/swap 排成
`(price, sequence)` 升序。空槽视作正无穷，所以会被推到尾部。

这是 free-funds 挂单：`baseFree → baseLocked`。驱逐先把旧 maker 的 base 解锁。
传进来已经过期的 TIF 是成功 no-op，不占 sequence。
-/
def postAskWithClientAt (s : State)
    (trader price size clientOrderIdLo clientOrderIdHi lastSlot lastTime nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  if price = 0 || size = 0 || maxOrderSequence ≤ s.sequence then
    .error .overflow
  else if expired lastSlot lastTime nowSlot nowTime then
    .ok (beginEvents s, 0)
  else Id.run do
    let mut st := { s with
      matchStopped := 0, matchError := 0
      matchLevel := 0
      eventCount := 0, lastEvent := .uninitialized }
    for i in [0:17] do
      if i < 4 then
        if st.matchStopped = (0 : UInt64) then
          let j : Nat := i
          if st.sizes[j]! = (0 : UInt64) then
            st := postAskFunds st trader 0 0 size
            st := { st with
              priceTicks := st.priceTicks.set (j % 4) price
              sequences := st.sequences.set (j % 4) st.sequence
              traders := st.traders.set (j % 4) trader
              sizes := st.sizes.set (j % 4) size
              lastSlots := st.lastSlots.set (j % 4) lastSlot
              lastTimes := st.lastTimes.set (j % 4) lastTime
              sequence := st.sequence + 1
              matchStopped := 1 }
      else if i = 4 then
        if st.matchStopped = (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            let oldSize := st.sizes[3]!
            let oldPrice := st.priceTicks[3]!
            if price < oldPrice then
              st := postAskFunds st trader st.traders[3]! oldSize size
              st := { st with
                priceTicks := st.priceTicks.set 3 price
                sequences := st.sequences.set 3 st.sequence
                traders := st.traders.set 3 trader
                sizes := st.sizes.set 3 size
                lastSlots := st.lastSlots.set 3 lastSlot
                lastTimes := st.lastTimes.set 3 lastTime
                sequence := st.sequence + 1
                matchStopped := 1
                matchLevel := 1 }
            else
              st := { st with matchError := 1 }
      else if i < 14 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            let j : Nat := (i - 5) % 3
            let r : Nat := j + 1
            let leftSize : UInt64 := st.sizes[j]!
            let rightSize : UInt64 := st.sizes[r]!
            if rightSize ≠ (0 : UInt64) then
              let leftPrice : UInt64 := st.priceTicks[j]!
              let rightPrice : UInt64 := st.priceTicks[r]!
              let leftSequence : UInt64 := st.sequences[j]!
              let rightSequence : UInt64 := st.sequences[r]!
              if leftSize = (0 : UInt64) then
                st := swapAskAdjacent st j
              else if rightPrice < leftPrice then
                st := swapAskAdjacent st j
              else if rightPrice = leftPrice then
                if rightSequence < leftSequence then
                  st := swapAskAdjacent st j
      else if i = 14 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            if st.matchLevel = (1 : UInt64) then
              st := appendEvent st
                (.evict s.traders[3]! s.sequences[3]! s.priceTicks[3]! s.sizes[3]!)
      else if i = 15 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            st := appendEvent st
              (.place s.sequence clientOrderIdLo clientOrderIdHi price size)
      else if i = 16 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            if lastSlot ≠ 0 || lastTime ≠ 0 then
              st := appendEvent st (.timeInForce s.sequence lastSlot lastTime)
    if st.matchError ≠ 0 || st.matchStopped = 0 then
      .error .overflow
    else
      .ok ({ st with matchStopped := 0, matchError := 0, matchLevel := 0 }, size)

attribute [pf_inline] postAskWithClientAt

/-- 兼容宿主调用：client order id 为零。 -/
def postAskAt (s : State) (trader price size lastSlot lastTime nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  postAskWithClientAt s trader price size 0 0 lastSlot lastTime nowSlot nowTime

attribute [pf_inline] postAskAt

/--
链上 free-funds ask 挂单；owner 由 account 1 signer 的完整 Pubkey 解析，slot/time
在入口各读取一次。调用者不能传入其他 trader 的内部 address。
-/
@[pf_entry]
def postAsk (s : State)
    (price size clientOrderIdLo clientOrderIdHi lastSlot lastTime : UInt64) :
    Except Error (State × UInt64) := do
  let trader ← requireTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  postAskWithClientAt s trader price size clientOrderIdLo clientOrderIdHi
    lastSlot lastTime clockSlot unixTime

/-- 兼容宿主调用：匿名 trader、无 TIF。 -/
def postAskFull (s : State) (price size : UInt64) : Except Error (State × UInt64) :=
  postAskAt s 0 price size 0 0 0 0

/-- `tickSize * price * baseLots`，在 UInt64 剖面内 fail closed。 -/
private def adjustedQuoteFor (s : State) (price size : UInt64) : Except Error UInt64 :=
  if size = 0 then .ok 0
  else if price = 0 then .error .overflow
  else if s.tickSize ≤ u64Max / price then
    let quotePerBase := s.tickSize * price
    if quotePerBase = 0 || size > u64Max / quotePerBase then .error .overflow
    else .ok (quotePerBase * size)
  else .error .overflow

/-- bid 的 quote collateral：`floor(tickSize * price * baseLots / baseLotsPerBaseUnit)`。 -/
private def bidCollateral (s : State) (price size : UInt64) : Except Error UInt64 := do
  if s.baseLotsPerBaseUnit = 0 then .error .overflow
  else .ok ((← adjustedQuoteFor s price size) / s.baseLotsPerBaseUnit)

attribute [pf_inline] adjustedQuoteFor bidCollateral

private def swapBidAdjacent (s : State) (j : Nat) : State :=
  let r := j + 1
  { s with
    bidPriceTicks :=
      (s.bidPriceTicks.set (j % 4) s.bidPriceTicks[r]!).set (r % 4) s.bidPriceTicks[j]!
    bidSequences :=
      (s.bidSequences.set (j % 4) s.bidSequences[r]!).set (r % 4) s.bidSequences[j]!
    bidTraders :=
      (s.bidTraders.set (j % 4) s.bidTraders[r]!).set (r % 4) s.bidTraders[j]!
    bidSizes :=
      (s.bidSizes.set (j % 4) s.bidSizes[r]!).set (r % 4) s.bidSizes[j]!
    bidLastSlots :=
      (s.bidLastSlots.set (j % 4) s.bidLastSlots[r]!).set (r % 4) s.bidLastSlots[j]!
    bidLastTimes :=
      (s.bidLastTimes.set (j % 4) s.bidLastTimes[r]!).set (r % 4) s.bidLastTimes[j]! }

attribute [pf_inline] swapBidAdjacent

/--
固定容量 bid 插入。订单 ID 存官方编码 `~~~sequence`，投影按价格和编码序号降序；
满书时只有更高价能驱逐最差 bid。free-funds collateral 从 quoteFree 锁进
quoteLocked，驱逐则按原价准确解锁旧订单。
-/
def postBidWithClientAt (s : State)
    (trader price size clientOrderIdLo clientOrderIdHi lastSlot lastTime nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  if price = 0 || size = 0 || maxOrderSequence ≤ s.sequence then
    .error .overflow
  else if expired lastSlot lastTime nowSlot nowTime then
    .ok (beginEvents s, 0)
  else do
    let newLock ← bidCollateral s price size
    let oldLock ← bidCollateral s s.bidPriceTicks[3]! s.bidSizes[3]!
    Id.run do
      let mut st := { s with
        matchStopped := 0, matchError := 0
        matchLevel := 0
        eventCount := 0, lastEvent := .uninitialized }
      for i in [0:17] do
        if i < 4 then
          if st.matchStopped = (0 : UInt64) then
            let j : Nat := i
            if st.bidSizes[j]! = (0 : UInt64) then
              st := postBidFunds st trader 0 0 newLock
              st := { st with
                bidPriceTicks := st.bidPriceTicks.set (j % 4) price
                bidSequences := st.bidSequences.set (j % 4) (~~~st.sequence)
                bidTraders := st.bidTraders.set (j % 4) trader
                bidSizes := st.bidSizes.set (j % 4) size
                bidLastSlots := st.bidLastSlots.set (j % 4) lastSlot
                bidLastTimes := st.bidLastTimes.set (j % 4) lastTime
                sequence := st.sequence + 1
                matchStopped := 1 }
        else if i = 4 then
          if st.matchStopped = (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              let oldPrice := st.bidPriceTicks[3]!
              if oldPrice < price then
                st := postBidFunds st trader st.bidTraders[3]! oldLock newLock
                st := { st with
                  bidPriceTicks := st.bidPriceTicks.set 3 price
                  bidSequences := st.bidSequences.set 3 (~~~st.sequence)
                  bidTraders := st.bidTraders.set 3 trader
                  bidSizes := st.bidSizes.set 3 size
                  bidLastSlots := st.bidLastSlots.set 3 lastSlot
                  bidLastTimes := st.bidLastTimes.set 3 lastTime
                  sequence := st.sequence + 1
                  matchStopped := 1
                  matchLevel := 1 }
              else
                st := { st with matchError := 1 }
        else if i < 14 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              let j : Nat := (i - 5) % 3
              let r : Nat := j + 1
              let leftSize : UInt64 := st.bidSizes[j]!
              let rightSize : UInt64 := st.bidSizes[r]!
              if rightSize ≠ (0 : UInt64) then
                let leftPrice : UInt64 := st.bidPriceTicks[j]!
                let rightPrice : UInt64 := st.bidPriceTicks[r]!
                let leftSequence : UInt64 := st.bidSequences[j]!
                let rightSequence : UInt64 := st.bidSequences[r]!
                if leftSize = (0 : UInt64) then
                  st := swapBidAdjacent st j
                else if leftPrice < rightPrice then
                  st := swapBidAdjacent st j
                else if rightPrice = leftPrice then
                  if leftSequence < rightSequence then
                    st := swapBidAdjacent st j
        else if i = 14 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              if st.matchLevel = (1 : UInt64) then
                st := appendEvent st
                  (.evict s.bidTraders[3]! (~~~s.bidSequences[3]!)
                    s.bidPriceTicks[3]! s.bidSizes[3]!)
        else if i = 15 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              st := appendEvent st
                (.place s.sequence clientOrderIdLo clientOrderIdHi price size)
        else if i = 16 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              if lastSlot ≠ 0 || lastTime ≠ 0 then
                st := appendEvent st (.timeInForce s.sequence lastSlot lastTime)
      if st.matchError ≠ 0 || st.matchStopped = 0 then
        .error .overflow
      else
        .ok ({ st with matchStopped := 0, matchError := 0, matchLevel := 0 }, size)

attribute [pf_inline] postBidWithClientAt

/-- 兼容宿主调用：client order id 为零。 -/
def postBidAt (s : State) (trader price size lastSlot lastTime nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  postBidWithClientAt s trader price size 0 0 lastSlot lastTime nowSlot nowTime

attribute [pf_inline] postBidAt

/-- Bid-side signer adapter；不能以 instruction 参数伪造 resting-order owner。 -/
@[pf_entry]
def postBid (s : State)
    (price size clientOrderIdLo clientOrderIdHi lastSlot lastTime : UInt64) :
    Except Error (State × UInt64) := do
  let trader ← requireTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  postBidWithClientAt s trader price size clientOrderIdLo clientOrderIdHi
    lastSlot lastTime clockSlot unixTime

/-- 扫书期间的瞬时 `MatchingEngineResponse`。不进入账户 schema。 -/
structure MatchAcc where
  sizes : Vector UInt64 4
  targetBase : UInt64
  filledBase : UInt64
  adjustedQuote : UInt64
  expiredBase : UInt64
  stopped : Bool
  events : Vector MarketEvent 5
  eventCount : UInt64
  lastEvent : MarketEvent
  deriving Repr, DecidableEq

private def MatchAcc.pushEvent (acc : MatchAcc) (event : MarketEvent) : MatchAcc :=
  if h : acc.eventCount.toNat < 5 then
    { acc with
      events := acc.events.set acc.eventCount.toNat event
      eventCount := acc.eventCount + 1
      lastEvent := event }
  else
    acc

/--
沿 ask 树中序投影做至多四档的 IOC。过期单取消并继续；第一档超限即停止；
整档成交继续，部分成交终止。所有乘加都在 UInt64 剖面内 fail-closed。
-/
private def scanAsks (s : State) (taker limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior)
    (fuel i : Nat) (acc : MatchAcc) : Except Error MatchAcc :=
  match fuel with
  | 0 => .ok acc
  | fuel' + 1 =>
    if acc.stopped || acc.filledBase = acc.targetBase then
      .ok acc
    else if h : i < 4 then
      let size := acc.sizes[i]
      if size = 0 then
        scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1) acc
      else if expired s.lastSlots[i] s.lastTimes[i] nowSlot nowTime then
        if acc.expiredBase ≤ u64Max - size then
          let next := acc.pushEvent
            (.expiredOrder s.traders[i] s.sequences[i] s.priceTicks[i] size)
          scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1)
            { next with
              sizes := acc.sizes.set i 0
              expiredBase := acc.expiredBase + size }
        else
          .error .overflow
      else if limit < s.priceTicks[i] then
        .ok { acc with stopped := true }
      else if s.traders[i] = taker then
        match behavior with
        | .abort => .error .overflow
        | .cancelProvide =>
          if acc.expiredBase ≤ u64Max - size then
            let next := acc.pushEvent (.reduce s.sequences[i] s.priceTicks[i] size 0)
            scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1)
              { next with
                sizes := acc.sizes.set i 0
                expiredBase := acc.expiredBase + size }
          else
            .error .overflow
        | .decrementTake =>
          let remaining := acc.targetBase - acc.filledBase
          let reduced := if remaining ≤ size then remaining else size
          if acc.expiredBase ≤ u64Max - reduced then
            let next := acc.pushEvent
              (.reduce s.sequences[i] s.priceTicks[i] reduced (size - reduced))
            scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1)
              { next with
                sizes := acc.sizes.set i (size - reduced)
                targetBase := acc.targetBase - reduced
                expiredBase := acc.expiredBase + reduced
                stopped := reduced = remaining }
          else
            .error .overflow
      else
        let remaining := acc.targetBase - acc.filledBase
        let fill := if remaining ≤ size then remaining else size
        let price := s.priceTicks[i]
        if price = 0 || s.tickSize ≤ u64Max / price then
          let quotePerBase := price * s.tickSize
          if quotePerBase = 0 || fill ≤ u64Max / quotePerBase then
            let quote := quotePerBase * fill
            if acc.adjustedQuote ≤ u64Max - quote then
              let next := acc.pushEvent
                (.fill s.traders[i] s.sequences[i] price fill (size - fill))
              scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1)
                { next with
                  sizes := acc.sizes.set i (size - fill)
                  targetBase := acc.targetBase
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
private def settleBuy (s : State) (clientOrderIdLo clientOrderIdHi : UInt64)
    (acc : MatchAcc) : Except Error (State × UInt64) :=
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
            let settled := { s with
              sizes := acc.sizes
              quoteLocked := s.quoteLocked - quoteDebit
              quoteFree := s.quoteFree + quoteLots
              baseLocked := s.baseLocked - makerBaseDebit
              baseFree := s.baseFree + baseCredit
              unclaimedFees := s.unclaimedFees + feeLots
              events := acc.events
              eventCount := acc.eventCount
              lastEvent := acc.lastEvent }
            .ok (appendEvent settled
                (.fillSummary clientOrderIdLo clientOrderIdHi acc.filledBase quoteLots feeLots),
              acc.filledBase)

/--
可测试的完整 N=4 IOC：红黑树中序跨档、严格 slot/time TIF、聚合费用和余额记账。
无流动性或首个有效价格超限是成功的零成交 IOC，不伪装成 overflow。
-/
def swapBuyForClientAt (s : State)
    (taker clientOrderIdLo clientOrderIdHi want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) :
    Except Error (State × UInt64) := do
  let s := beginEvents s
  let acc ← scanAsks s taker limit nowSlot nowTime behavior 4 0
    { sizes := s.sizes, targetBase := want, filledBase := 0, adjustedQuote := 0,
      expiredBase := 0, stopped := false, events := s.events,
      eventCount := s.eventCount, lastEvent := s.lastEvent }
  settleBuy s clientOrderIdLo clientOrderIdHi acc

/-- 兼容宿主调用：client order id 为零。 -/
def swapBuyForAt (s : State) (taker want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) : Except Error (State × UInt64) :=
  swapBuyForClientAt s taker 0 0 want limit nowSlot nowTime behavior

/-- 无自成交身份的兼容入口。 -/
def swapBuyAt (s : State) (want limit nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  swapBuyForAt s u64Max want limit nowSlot nowTime .abort

/-- sell IOC 扫 bid 时的宿主 accumulator。 -/
structure SellAcc where
  sizes : Vector UInt64 4
  targetBase : UInt64
  filledBase : UInt64
  adjustedQuote : UInt64
  makerQuote : UInt64
  unlockedQuote : UInt64
  stopped : Bool
  events : Vector MarketEvent 5
  eventCount : UInt64
  lastEvent : MarketEvent
  deriving Repr, DecidableEq

private def SellAcc.pushEvent (acc : SellAcc) (event : MarketEvent) : SellAcc :=
  if h : acc.eventCount.toNat < 5 then
    { acc with
      events := acc.events.set acc.eventCount.toNat event
      eventCount := acc.eventCount + 1
      lastEvent := event }
  else
    acc

private def scanBids (s : State) (taker limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior)
    (fuel i : Nat) (acc : SellAcc) : Except Error SellAcc :=
  match fuel with
  | 0 => .ok acc
  | fuel' + 1 => do
    if acc.stopped || acc.filledBase = acc.targetBase then
      .ok acc
    else if h : i < 4 then
      let size := acc.sizes[i]
      if size = 0 then
        scanBids s taker limit nowSlot nowTime behavior fuel' (i + 1) acc
      else if expired s.bidLastSlots[i] s.bidLastTimes[i] nowSlot nowTime then
        let unlocked ← bidCollateral s s.bidPriceTicks[i] size
        if acc.unlockedQuote ≤ u64Max - unlocked then
          let next := acc.pushEvent
            (.expiredOrder s.bidTraders[i] (~~~s.bidSequences[i]) s.bidPriceTicks[i] size)
          scanBids s taker limit nowSlot nowTime behavior fuel' (i + 1)
            { next with
              sizes := acc.sizes.set i 0
              unlockedQuote := acc.unlockedQuote + unlocked }
        else
          .error .overflow
      else if s.bidPriceTicks[i] < limit then
        .ok { acc with stopped := true }
      else if s.bidTraders[i] = taker then
        match behavior with
        | .abort => .error .overflow
        | .cancelProvide =>
          let unlocked ← bidCollateral s s.bidPriceTicks[i] size
          if acc.unlockedQuote ≤ u64Max - unlocked then
            let next := acc.pushEvent
              (.reduce (~~~s.bidSequences[i]) s.bidPriceTicks[i] size 0)
            scanBids s taker limit nowSlot nowTime behavior fuel' (i + 1)
              { next with
                sizes := acc.sizes.set i 0
                unlockedQuote := acc.unlockedQuote + unlocked }
          else
            .error .overflow
        | .decrementTake =>
          let remaining := acc.targetBase - acc.filledBase
          let reduced := if remaining ≤ size then remaining else size
          let unlocked ← bidCollateral s s.bidPriceTicks[i] reduced
          if acc.unlockedQuote ≤ u64Max - unlocked then
            let next := acc.pushEvent
              (.reduce (~~~s.bidSequences[i]) s.bidPriceTicks[i] reduced (size - reduced))
            scanBids s taker limit nowSlot nowTime behavior fuel' (i + 1)
              { next with
                sizes := acc.sizes.set i (size - reduced)
                targetBase := acc.targetBase - reduced
                unlockedQuote := acc.unlockedQuote + unlocked
                stopped := reduced = remaining }
          else
            .error .overflow
      else
        let remaining := acc.targetBase - acc.filledBase
        let fill := if remaining ≤ size then remaining else size
        let adjusted ← adjustedQuoteFor s s.bidPriceTicks[i] fill
        let makerQuote ← bidCollateral s s.bidPriceTicks[i] fill
        if acc.adjustedQuote > u64Max - adjusted || acc.makerQuote > u64Max - makerQuote then
          .error .overflow
        else
          let next := acc.pushEvent
            (.fill s.bidTraders[i] (~~~s.bidSequences[i]) s.bidPriceTicks[i] fill (size - fill))
          scanBids s taker limit nowSlot nowTime behavior fuel' (i + 1)
            { next with
              sizes := acc.sizes.set i (size - fill)
              targetBase := acc.targetBase
              filledBase := acc.filledBase + fill
              adjustedQuote := acc.adjustedQuote + adjusted
              makerQuote := acc.makerQuote + makerQuote
              unlockedQuote := acc.unlockedQuote
              stopped := fill = remaining }
    else
      .ok acc

private def settleSell (s : State) (clientOrderIdLo clientOrderIdHi : UInt64)
    (acc : SellAcc) : Except Error (State × UInt64) :=
  if s.baseLotsPerBaseUnit = 0 then
    .error .overflow
  else if acc.adjustedQuote ≠ 0 && s.takerFeeBps > u64Max / acc.adjustedQuote then
    .error .overflow
  else
    let grossQuote := acc.adjustedQuote / s.baseLotsPerBaseUnit
    let adjustedFee := ceilDiv (acc.adjustedQuote * s.takerFeeBps) 10000
    let feeLots := ceilDiv adjustedFee s.baseLotsPerBaseUnit
    if grossQuote < feeLots then
      .error .overflow
    else if acc.makerQuote > u64Max - acc.unlockedQuote then
      .error .overflow
    else
      let quoteDebit := acc.makerQuote + acc.unlockedQuote
      let takerQuote := grossQuote - feeLots
      if quoteDebit > s.quoteLocked || acc.filledBase > s.baseFree then
        .error .overflow
      else if takerQuote > u64Max - acc.unlockedQuote then
        .error .overflow
      else
        let quoteCredit := takerQuote + acc.unlockedQuote
        if s.quoteFree > u64Max - quoteCredit then
          .error .overflow
        else if s.unclaimedFees > u64Max - feeLots then
          .error .overflow
        else
          let _ :=
            if acc.filledBase = 0 then 0
            else tokenTransferChecked acc.filledBase 6
          let settled := { s with
            bidSizes := acc.sizes
            quoteLocked := s.quoteLocked - quoteDebit
            quoteFree := s.quoteFree + quoteCredit
            unclaimedFees := s.unclaimedFees + feeLots
            events := acc.events
            eventCount := acc.eventCount
            lastEvent := acc.lastEvent }
          .ok (appendEvent settled
              (.fillSummary clientOrderIdLo clientOrderIdHi acc.filledBase grossQuote feeLots),
            acc.filledBase)

/-- 可测试的 N=4 sell IOC 宿主语义。 -/
def swapSellForClientAt (s : State)
    (taker clientOrderIdLo clientOrderIdHi want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) : Except Error (State × UInt64) := do
  let s := beginEvents s
  let acc ← scanBids s taker limit nowSlot nowTime behavior 4 0
    { sizes := s.bidSizes, targetBase := want, filledBase := 0, adjustedQuote := 0,
      makerQuote := 0, unlockedQuote := 0, stopped := false, events := s.events,
      eventCount := s.eventCount, lastEvent := s.lastEvent }
  settleSell s clientOrderIdLo clientOrderIdHi acc

/-- 兼容宿主调用：client order id 为零。 -/
def swapSellForAt (s : State) (taker want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) : Except Error (State × UInt64) :=
  swapSellForClientAt s taker 0 0 want limit nowSlot nowTime behavior

def swapSellAt (s : State) (want limit nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  swapSellForAt s u64Max want limit nowSlot nowTime .abort

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
                  let settled := { s with
                    quoteLocked := s.quoteLocked - quoteDebit
                    quoteFree := s.quoteFree + quoteLots
                    baseLocked := s.baseLocked - baseDebit
                    baseFree := s.baseFree + baseDebit
                    unclaimedFees := s.unclaimedFees + feeLots }
                  .ok (settled, s.matchFilled)
                else
                  let _ := tokenTransferChecked s.matchFilled 6
                  let settled := { s with
                    quoteLocked := s.quoteLocked - quoteDebit
                    quoteFree := s.quoteFree + quoteLots
                    baseLocked := s.baseLocked - baseDebit
                    baseFree := s.baseFree + baseDebit
                    unclaimedFees := s.unclaimedFees + feeLots }
                  .ok (settled, s.matchFilled)
              else .error .overflow
            else .error .overflow
          else .error .overflow
        else .error .overflow
      else .error .overflow
    else .error .overflow
  else .error .overflow

private def settleFold (s : State) : Except Error (State × UInt64) :=
  if s.matchError ≠ 0 then .error .overflow
  else finishFold s s.matchMakerQuote s.matchLimit

attribute [pf_inline] finishFold settleFold

/--
链上 N=4 IOC。`behavior`：0=Abort、1=CancelProvide、2=DecrementTake。
十九次 state-carrying bounded fold：第 0 次清瞬时响应，接着十六次按四档 ×
（slot TIF、time TIF、撮合、advance）推进，第 17 次计算结算数值，第 18 次追加
summary。把算术和动态 event write 分 phase，避免 checked-arithmetic continuation
复制动态 variant-vector write；循环 store 会继续下一次，不再静态复制后续档位。
-/
@[pf_entry]
def swapBuy (s : State)
    (taker behavior clientOrderIdLo clientOrderIdHi want limit : UInt64) :
    Except Error (State × UInt64) := Id.run do
  let mut st := beginEvents s
  for i in [0:19] do
    if i = 0 then
      st := { st with
        matchFilled := 0, matchQuote := 0, matchMakerQuote := 0, matchExpired := 0,
        matchStopped := 0, matchError := 0, matchLevel := 0,
        matchWant := want, matchLimit := limit }
    else if i = 17 then
      if st.matchError = 0 then
        if st.baseLotsPerBaseUnit = 0 then
          st := { st with matchError := 1 }
        else if st.matchQuote = 0 then
          st := { st with matchMakerQuote := 0, matchLimit := 0 }
        else
          let quoteLots := (st.matchQuote - 1) / st.baseLotsPerBaseUnit + 1
          if st.takerFeeBps = 0 then
            st := { st with matchMakerQuote := quoteLots, matchLimit := 0 }
          else if st.takerFeeBps ≤ u64Max / st.matchQuote then
            let feeProduct := st.matchQuote * st.takerFeeBps
            let adjustedFee := (feeProduct - 1) / 10000 + 1
            let feeLots := (adjustedFee - 1) / st.baseLotsPerBaseUnit + 1
            st := { st with matchMakerQuote := quoteLots, matchLimit := feeLots }
          else
            st := { st with matchError := 1 }
    else if i = 18 then
      if st.matchError = 0 then
        st := appendEvent st
          (.fillSummary clientOrderIdLo clientOrderIdHi
            st.matchFilled st.matchMakerQuote st.matchLimit)
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
                let expiredState := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchExpired := st.matchExpired + size }
                st := appendEvent expiredState
                  (.expiredOrder st.traders[j]! st.sequences[j]! st.priceTicks[j]! size)
              else
                st := { st with matchStopped := 1, matchError := 1 }
        else if phase = 1 then
          if st.lastTimes[j]! ≠ 0 then
            if st.lastTimes[j]! < unixTime then
              if st.matchExpired ≤ u64Max - size then
                let expiredState := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchExpired := st.matchExpired + size }
                st := appendEvent expiredState
                  (.expiredOrder st.traders[j]! st.sequences[j]! st.priceTicks[j]! size)
              else
                st := { st with matchStopped := 1, matchError := 1 }
        else if phase = 2 then
          if st.matchLimit < st.priceTicks[j]! then
            st := { st with matchStopped := 1 }
          else if st.traders[j]! = taker then
            if behavior = 0 then
              st := { st with matchStopped := 1, matchError := 1 }
            else if behavior = 1 then
              if st.matchExpired ≤ u64Max - size then
                let reducedState := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchExpired := st.matchExpired + size }
                st := appendEvent reducedState
                  (.reduce st.sequences[j]! st.priceTicks[j]! size 0)
              else
                st := { st with matchStopped := 1, matchError := 1 }
            else if behavior = 2 then
              let remaining := st.matchWant - st.matchFilled
              if remaining ≤ size then
                if st.matchExpired ≤ u64Max - remaining then
                  let reducedState := { st with
                    sizes := st.sizes.set (j % 4) (size - remaining)
                    matchExpired := st.matchExpired + remaining
                    matchWant := st.matchWant - remaining
                    matchStopped := 1 }
                  st := appendEvent reducedState
                    (.reduce st.sequences[j]! st.priceTicks[j]! remaining (size - remaining))
                else
                  st := { st with matchStopped := 1, matchError := 1 }
              else
                if st.matchExpired ≤ u64Max - size then
                  let reducedState := { st with
                    sizes := st.sizes.set (j % 4) 0
                    matchExpired := st.matchExpired + size
                    matchWant := st.matchWant - size }
                  st := appendEvent reducedState
                    (.reduce st.sequences[j]! st.priceTicks[j]! size 0)
                else
                  st := { st with matchStopped := 1, matchError := 1 }
            else
              st := { st with matchStopped := 1, matchError := 1 }
          else
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let fill := remaining
              let price := st.priceTicks[j]!
              if price = 0 then
                let filledState := { st with
                  sizes := st.sizes.set (j % 4) (size - fill)
                  matchFilled := st.matchFilled + fill
                  matchStopped := 1 }
                st := appendEvent filledState
                  (.fill st.traders[j]! st.sequences[j]! price fill (size - fill))
              else if st.tickSize ≤ u64Max / price then
                let quotePerBase := price * st.tickSize
                if quotePerBase = 0 then
                  let filledState := { st with
                    sizes := st.sizes.set (j % 4) (size - fill)
                    matchFilled := st.matchFilled + fill
                    matchStopped := 1 }
                  st := appendEvent filledState
                    (.fill st.traders[j]! st.sequences[j]! price fill (size - fill))
                else if fill ≤ u64Max / quotePerBase then
                  let quote := quotePerBase * fill
                  if st.matchQuote ≤ u64Max - quote then
                    let filledState := { st with
                      sizes := st.sizes.set (j % 4) (size - fill)
                      matchFilled := st.matchFilled + fill
                      matchQuote := st.matchQuote + quote
                      matchStopped := 1 }
                    st := appendEvent filledState
                      (.fill st.traders[j]! st.sequences[j]! price fill (size - fill))
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
                let filledState := { st with
                  sizes := st.sizes.set (j % 4) 0
                  matchFilled := st.matchFilled + fill }
                st := appendEvent filledState
                  (.fill st.traders[j]! st.sequences[j]! price fill 0)
              else if st.tickSize ≤ u64Max / price then
                let quotePerBase := price * st.tickSize
                if quotePerBase = 0 then
                  let filledState := { st with
                    sizes := st.sizes.set (j % 4) 0
                    matchFilled := st.matchFilled + fill }
                  st := appendEvent filledState
                    (.fill st.traders[j]! st.sequences[j]! price fill 0)
                else if fill ≤ u64Max / quotePerBase then
                  let quote := quotePerBase * fill
                  if st.matchQuote ≤ u64Max - quote then
                    let filledState := { st with
                      sizes := st.sizes.set (j % 4) 0
                      matchFilled := st.matchFilled + fill
                      matchQuote := st.matchQuote + quote }
                    st := appendEvent filledState
                      (.fill st.traders[j]! st.sequences[j]! price fill 0)
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
                else
                  st := { st with matchStopped := 1, matchError := 1 }
              else
                st := { st with matchStopped := 1, matchError := 1 }
  settleFold st

/-- sell fold 中减少 resting bid，并累计要解锁的 quote collateral。 -/
private def unlockBidFold (s : State) (j : Nat) (amount : UInt64) : State :=
  let size := s.bidSizes[j]!
  let price := s.bidPriceTicks[j]!
  if size < amount then
    { s with matchStopped := 1, matchError := 1 }
  else if s.baseLotsPerBaseUnit = 0 then
    { s with matchStopped := 1, matchError := 1 }
  else if price = 0 then
    { s with matchStopped := 1, matchError := 1 }
  else if s.tickSize ≤ u64Max / price then
    let quotePerBase := s.tickSize * price
    if quotePerBase = 0 then
      { s with matchStopped := 1, matchError := 1 }
    else if amount > u64Max / quotePerBase then
      { s with matchStopped := 1, matchError := 1 }
    else
      let unlocked := (quotePerBase * amount) / s.baseLotsPerBaseUnit
      if s.matchExpired ≤ u64Max - unlocked then
        { s with
          bidSizes := s.bidSizes.set (j % 4) (size - amount)
          matchExpired := s.matchExpired + unlocked }
      else
        { s with matchStopped := 1, matchError := 1 }
  else
    { s with matchStopped := 1, matchError := 1 }

/-- sell fold 中成交 resting bid，并累计 adjusted quote 和 maker quote debit。 -/
private def fillBidFold (s : State) (j : Nat) (fill : UInt64) : State :=
  let size := s.bidSizes[j]!
  let price := s.bidPriceTicks[j]!
  if size < fill then
    { s with matchStopped := 1, matchError := 1 }
  else if s.baseLotsPerBaseUnit = 0 then
    { s with matchStopped := 1, matchError := 1 }
  else if price = 0 then
    { s with matchStopped := 1, matchError := 1 }
  else if s.tickSize ≤ u64Max / price then
    let quotePerBase := s.tickSize * price
    if quotePerBase = 0 then
      { s with matchStopped := 1, matchError := 1 }
    else if fill > u64Max / quotePerBase then
      { s with matchStopped := 1, matchError := 1 }
    else
      let adjusted := quotePerBase * fill
      let makerQuote := adjusted / s.baseLotsPerBaseUnit
      if s.matchQuote > u64Max - adjusted then
        { s with matchStopped := 1, matchError := 1 }
      else if s.matchMakerQuote > u64Max - makerQuote then
        { s with matchStopped := 1, matchError := 1 }
      else if s.matchFilled > u64Max - fill then
        { s with matchStopped := 1, matchError := 1 }
      else
        { s with
          bidSizes := s.bidSizes.set (j % 4) (size - fill)
          matchFilled := s.matchFilled + fill
          matchQuote := s.matchQuote + adjusted
          matchMakerQuote := s.matchMakerQuote + makerQuote }
  else
    { s with matchStopped := 1, matchError := 1 }

attribute [pf_inline] unlockBidFold fillBidFold

private def commitSellFold (s : State) (grossQuote feeLots : UInt64) :
    Except Error (State × UInt64) :=
  if grossQuote < feeLots then .error .overflow
  else if s.matchMakerQuote > u64Max - s.matchExpired then .error .overflow
  else
    let quoteDebit := s.matchMakerQuote + s.matchExpired
    let takerQuote := grossQuote - feeLots
    if quoteDebit > s.quoteLocked then .error .overflow
    else if s.matchFilled > s.baseFree then .error .overflow
    else if takerQuote > u64Max - s.matchExpired then .error .overflow
    else
      let quoteCredit := takerQuote + s.matchExpired
      if s.quoteFree > u64Max - quoteCredit then .error .overflow
      else if s.unclaimedFees > u64Max - feeLots then .error .overflow
      else if s.matchFilled = 0 then
        let settled := { s with
          quoteLocked := s.quoteLocked - quoteDebit
          quoteFree := s.quoteFree + quoteCredit
          unclaimedFees := s.unclaimedFees + feeLots }
        .ok (settled, s.matchFilled)
      else
        let _ := tokenTransferChecked s.matchFilled 6
        let settled := { s with
          quoteLocked := s.quoteLocked - quoteDebit
          quoteFree := s.quoteFree + quoteCredit
          unclaimedFees := s.unclaimedFees + feeLots }
        .ok (settled, s.matchFilled)

private def settleSellFold (s : State) : Except Error (State × UInt64) :=
  if s.matchError ≠ 0 then .error .overflow
  else commitSellFold s s.matchLimit s.matchWant

attribute [pf_inline] commitSellFold settleSellFold

/--
链上 N=4 sell IOC。每档拆为 slot TIF、time TIF、撮合、event flush、advance
五个 phase；随后计算并追加 summary。`matchStopped` 的 2/3 临时表示“待发事件后
继续/停止”，flush 后归一为 0/1。这样 helper 结果先跨迭代物化，再做动态写。
-/
@[pf_entry]
def swapSell (s : State)
    (taker behavior clientOrderIdLo clientOrderIdHi want limit : UInt64) :
    Except Error (State × UInt64) := Id.run do
  let mut st := beginEvents s
  for i in [0:23] do
    if i = 0 then
      st := { st with
        matchFilled := 0, matchQuote := 0, matchMakerQuote := 0, matchExpired := 0,
        matchStopped := 0, matchError := 0, matchLevel := 0,
        matchWant := want, matchLimit := limit }
    else if i = 21 then
      if st.matchError = 0 then
        if st.baseLotsPerBaseUnit = 0 then
          st := { st with matchError := 1 }
        else
          let grossQuote := st.matchQuote / st.baseLotsPerBaseUnit
          if st.matchQuote = 0 then
            st := { st with matchLimit := grossQuote, matchWant := 0 }
          else if st.takerFeeBps = 0 then
            st := { st with matchLimit := grossQuote, matchWant := 0 }
          else if st.takerFeeBps ≤ u64Max / st.matchQuote then
            let feeProduct := st.matchQuote * st.takerFeeBps
            let adjustedFee := (feeProduct - 1) / 10000 + 1
            let feeLots := (adjustedFee - 1) / st.baseLotsPerBaseUnit + 1
            st := { st with matchLimit := grossQuote, matchWant := feeLots }
          else
            st := { st with matchError := 1 }
    else if i = 22 then
      if st.matchError = 0 then
        st := appendEvent st
          (.fillSummary clientOrderIdLo clientOrderIdHi
            st.matchFilled st.matchLimit st.matchWant)
    else
      let k := i - 1
      let phase := k % 5
      let j := st.matchLevel.toNat
      let size := st.bidSizes[j]!
      if phase = 3 then
        if st.matchError = 0 then
          if st.matchStopped = 2 then
            let event := st.lastEvent
            st := appendEvent { st with matchStopped := 0 } event
          else if st.matchStopped = 3 then
            let event := st.lastEvent
            st := appendEvent { st with matchStopped := 1 } event
      else if st.matchStopped = 0 then
        if st.matchFilled = st.matchWant then
          st := { st with matchStopped := 1 }
        else if phase = 4 then
          st := { st with matchLevel := st.matchLevel + 1 }
        else if size ≠ 0 then
          if phase = 0 then
            if st.bidLastSlots[j]! ≠ 0 then
              if st.bidLastSlots[j]! < clockSlot then
                let unlocked := unlockBidFold st j size
                st := { unlocked with
                  matchStopped := 2
                  lastEvent := .expiredOrder st.bidTraders[j]! (~~~st.bidSequences[j]!)
                    st.bidPriceTicks[j]! size }
          else if phase = 1 then
            if st.bidLastTimes[j]! ≠ 0 then
              if st.bidLastTimes[j]! < unixTime then
                let unlocked := unlockBidFold st j size
                st := { unlocked with
                  matchStopped := 2
                  lastEvent := .expiredOrder st.bidTraders[j]! (~~~st.bidSequences[j]!)
                    st.bidPriceTicks[j]! size }
          else if phase = 2 then
            if st.bidPriceTicks[j]! < st.matchLimit then
              st := { st with matchStopped := 1 }
            else if st.bidTraders[j]! = taker then
              if behavior = 0 then
                st := { st with matchStopped := 1, matchError := 1 }
              else if behavior = 1 then
                let unlocked := unlockBidFold st j size
                st := { unlocked with
                  matchStopped := 2
                  lastEvent := .reduce (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size 0 }
              else if behavior = 2 then
                let remaining := st.matchWant - st.matchFilled
                if remaining ≤ size then
                  let unlocked := unlockBidFold st j remaining
                  st := { unlocked with
                    matchWant := st.matchWant - remaining
                    matchStopped := 3
                    lastEvent := .reduce (~~~st.bidSequences[j]!) st.bidPriceTicks[j]!
                      remaining (size - remaining) }
                else
                  let unlocked := unlockBidFold st j size
                  st := { unlocked with
                    matchWant := st.matchWant - size
                    matchStopped := 2
                    lastEvent := .reduce (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size 0 }
              else
                st := { st with matchStopped := 1, matchError := 1 }
            else
              let remaining := st.matchWant - st.matchFilled
              if remaining ≤ size then
                let filled := fillBidFold st j remaining
                st := { filled with
                  matchStopped := 3
                  lastEvent := .fill st.bidTraders[j]! (~~~st.bidSequences[j]!)
                    st.bidPriceTicks[j]! remaining (size - remaining) }
              else
                let filled := fillBidFold st j size
                st := { filled with
                  matchStopped := 2
                  lastEvent := .fill st.bidTraders[j]! (~~~st.bidSequences[j]!)
                    st.bidPriceTicks[j]! size 0 }
  settleSellFold st

/--
官方 `reduce_order_inner` 的 ask-side bounded 版本：按 `(price, sequence)` 找订单，
校验内部 seat address，减少 `min(qty, restingSize)`，并把对应 trader 的 base
从 locked 解到 free。aggregate balance 暂时同步维护，供尚未迁移的 matching path
使用；它是 per-seat ledger 的兼容投影，不再是 owner 授权来源。
缺失订单成功返回 0；错误 owner、无效 seat 和账本不一致 fail closed。
-/
def reduceAskAt (s : State) (trader price sequence qty : UInt64) :
    Except Error (State × UInt64) :=
  if trader = 0 || 4 < trader then
    .error .overflow
  else
    let traderIndex := trader.toNat - 1
    if s.traderUsed[traderIndex]! = 0 then
      .error .overflow
    else Id.run do
      let s := beginEvents s
      if qty = 0 then
        .ok (s, 0)
      else
        let mut st := { s with matchFilled := 0, matchStopped := 0, matchError := 0 }
        for i in [0:4] do
          if st.matchStopped = (0 : UInt64) then
            let j : Nat := i
            let size : UInt64 := st.sizes[j]!
            if size ≠ (0 : UInt64) then
              if st.priceTicks[j]! = price then
                if st.sequences[j]! = sequence then
                  if st.traders[j]! = trader then
                    let removed := if qty ≤ size then qty else size
                    if removed ≤ st.traderBaseLocked[traderIndex]! then
                      if st.traderBaseFree[traderIndex]! ≤ u64Max - removed then
                        if removed ≤ st.baseLocked then
                          if st.baseFree ≤ u64Max - removed then
                            let reduced := { st with
                              sizes := st.sizes.set (j % 4) (size - removed)
                              traderBaseLocked := st.traderBaseLocked.set
                                (traderIndex % 4) (st.traderBaseLocked[traderIndex]! - removed)
                              traderBaseFree := st.traderBaseFree.set
                                (traderIndex % 4) (st.traderBaseFree[traderIndex]! + removed)
                              baseLocked := st.baseLocked - removed
                              baseFree := st.baseFree + removed
                              matchFilled := removed
                              matchStopped := 1 }
                            st := appendEvent reduced (.reduce sequence price removed (size - removed))
                          else
                            st := { st with matchStopped := 1, matchError := 1 }
                        else
                          st := { st with matchStopped := 1, matchError := 1 }
                      else
                        st := { st with matchStopped := 1, matchError := 1 }
                    else
                      st := { st with matchStopped := 1, matchError := 1 }
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
        if st.matchError ≠ 0 then
          .error .overflow
        else
          let reduced := st.matchFilled
          .ok ({ st with matchFilled := 0, matchStopped := 0, matchError := 0 }, reduced)

/-- bid reduce/cancel 按 encoded order id 查找，并按原价解锁 quote collateral。 -/
def reduceBidAt (s : State) (trader price sequence qty : UInt64) :
    Except Error (State × UInt64) :=
  if trader = 0 || 4 < trader then
    .error .overflow
  else
    let traderIndex := trader.toNat - 1
    if s.traderUsed[traderIndex]! = 0 then
      .error .overflow
    else Id.run do
      let s := beginEvents s
      if qty = 0 then
        .ok (s, 0)
      else
        let mut st := { s with
          matchFilled := 0, matchExpired := 0, matchStopped := 0, matchError := 0 }
        for i in [0:4] do
          if st.matchStopped = (0 : UInt64) then
            let j : Nat := i
            let size : UInt64 := st.bidSizes[j]!
            if size ≠ (0 : UInt64) then
              if st.bidPriceTicks[j]! = price then
                if st.bidSequences[j]! = sequence then
                  if st.bidTraders[j]! = trader then
                    let removed := if qty ≤ size then qty else size
                    st := unlockBidFold st j removed
                    let reduced := { st with matchFilled := removed, matchStopped := 1 }
                    st := appendEvent reduced (.reduce sequence price removed (size - removed))
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
        if st.matchError ≠ 0 then
          .error .overflow
        else if st.matchExpired > st.traderQuoteLocked[traderIndex]! then
          .error .overflow
        else if st.traderQuoteFree[traderIndex]! > u64Max - st.matchExpired then
          .error .overflow
        else if st.matchExpired > st.quoteLocked then
          .error .overflow
        else if st.quoteFree > u64Max - st.matchExpired then
          .error .overflow
        else
          let reduced := st.matchFilled
          .ok ({ st with
                  traderQuoteLocked := st.traderQuoteLocked.set (traderIndex % 4)
                    (st.traderQuoteLocked[traderIndex]! - st.matchExpired)
                  traderQuoteFree := st.traderQuoteFree.set (traderIndex % 4)
                    (st.traderQuoteFree[traderIndex]! + st.matchExpired)
                  quoteLocked := st.quoteLocked - st.matchExpired
                  quoteFree := st.quoteFree + st.matchExpired
                  matchFilled := 0, matchExpired := 0,
                  matchStopped := 0, matchError := 0 }, reduced)

attribute [pf_inline] reduceAskAt reduceBidAt

/-- SVM adapter：由 account 1 signer 的完整 Pubkey 解析 seat，不能伪造其他 owner。 -/
@[pf_entry]
def reduceAsk (s : State) (price sequence qty : UInt64) :
    Except Error (State × UInt64) := do
  let trader ← requireTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  reduceAskAt s trader price sequence qty

/-- Bid-side signer adapter；encoded sequence 仍原样传给 bounded order lookup。 -/
@[pf_entry]
def reduceBid (s : State) (price sequence qty : UInt64) :
    Except Error (State × UInt64) := do
  let trader ← requireTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  reduceBidAt s trader price sequence qty

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

/-- `CancelOrder` 是把指定订单 reduce 到 0。 -/
def cancelAsk (s : State) (trader price sequence : UInt64) :
    Except Error (State × UInt64) :=
  reduceAskAt s trader price sequence u64Max

def cancelBid (s : State) (trader price sequence : UInt64) :
    Except Error (State × UInt64) :=
  reduceBidAt s trader price sequence u64Max

/-- 收取当前全部未领取费用；返回本次转移的 quote lots。 -/
@[pf_entry]
def collectFees (s : State) : Except Error (State × UInt64) :=
  if s.collectedFees ≤ u64Max - s.unclaimedFees then
    let s := beginEvents s
    let settled := { s with
      collectedFees := s.collectedFees + s.unclaimedFees
      unclaimedFees := 0 }
    .ok (appendEvent settled (.fee s.unclaimedFees), s.unclaimedFees)
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
  if s.sizes[0]! ≠ 0 then s.priceTicks[0]!
  else if s.sizes[1]! ≠ 0 then s.priceTicks[1]!
  else if s.sizes[2]! ≠ 0 then s.priceTicks[2]!
  else if s.sizes[3]! ≠ 0 then s.priceTicks[3]!
  else 0

@[pf_entry]
def bestBid (s : State) : UInt64 :=
  if s.bidSizes[0]! ≠ 0 then s.bidPriceTicks[0]!
  else if s.bidSizes[1]! ≠ 0 then s.bidPriceTicks[1]!
  else if s.bidSizes[2]! ≠ 0 then s.bidPriceTicks[2]!
  else if s.bidSizes[3]! ≠ 0 then s.bidPriceTicks[3]!
  else 0

@[pf_entry]
def askQty (s : State) : UInt64 :=
  s.sizes[0]! + s.sizes[1]! + s.sizes[2]! + s.sizes[3]!

@[pf_entry]
def bidQty (s : State) : UInt64 :=
  s.bidSizes[0]! + s.bidSizes[1]! + s.bidSizes[2]! + s.bidSizes[3]!

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

@[pf_entry]
def eventCountOf (s : State) : UInt64 :=
  s.eventCount

@[pf_entry]
def lastEventKind (s : State) : UInt64 :=
  match s.lastEvent with
  | .uninitialized => 0
  | .fill _ _ _ _ _ => 1
  | .place _ _ _ _ _ => 2
  | .reduce _ _ _ _ => 3
  | .evict _ _ _ _ => 4
  | .fillSummary _ _ _ _ _ => 5
  | .fee _ => 6
  | .timeInForce _ _ _ => 7
  | .expiredOrder _ _ _ _ => 8

@[pf_entry]
def lastEventAmount (s : State) : UInt64 :=
  match s.lastEvent with
  | .uninitialized => 0
  | .fill _ _ _ filled _ => filled
  | .place _ _ _ _ placed => placed
  | .reduce _ _ removed _ => removed
  | .evict _ _ _ evicted => evicted
  | .fillSummary _ _ totalBase _ _ => totalBase
  | .fee fees => fees
  | .timeInForce _ lastValidSlot _ => lastValidSlot
  | .expiredOrder _ _ _ removed => removed

end Projects.Phoenix
