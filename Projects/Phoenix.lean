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
官方 `PhoenixMarketEvent` 的 bounded typed 形状。`header` 只保留 Borsh ordinal 1；
真实 `AuditLogHeader` 是 recorder 的独立 batch prefix，不写进本向量。maker-bearing
event 在构造前把内部 seat resolve 成四 limb Pubkey。官方 u16 event index 在这里以
UInt64 保存，但 `appendEvent` 在第 6 条时 fail-closed；wire adapter 再收窄成 little-endian u16。
-/
inductive MarketEvent where
  | uninitialized
  | header
  | fill (index maker0 maker1 maker2 maker3 orderSequence price filled remaining : UInt64)
  /-- `clientOrderIdLo` then `clientOrderIdHi` is the little-endian two-limb form of Phoenix's u128. -/
  | place (index orderSequence clientOrderIdLo clientOrderIdHi price placed : UInt64)
  | reduce (index orderSequence price removed remaining : UInt64)
  | evict (index maker0 maker1 maker2 maker3 orderSequence price evicted : UInt64)
  | fillSummary (index clientOrderIdLo clientOrderIdHi totalBase totalQuote totalFee : UInt64)
  | fee (index feesCollected : UInt64)
  | timeInForce (index orderSequence lastValidSlot lastValidTime : UInt64)
  | expiredOrder (index maker0 maker1 maker2 maker3 orderSequence price removed : UInt64)
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
  | unauthorized
  | full
  | selfTrade
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Fold / state-machine error codes. `0` is success. -/
def matchOverflow : UInt64 := 1
def matchFull : UInt64 := 2
def matchSelfTrade : UInt64 := 3
def matchUnauthorized : UInt64 := 4

private def errorOfMatch (code : UInt64) : Error :=
  if code = matchFull then .full
  else if code = matchSelfTrade then .selfTrade
  else if code = matchUnauthorized then .unauthorized
  else .overflow

/-- Extractable: the extractor only lowers concrete `.error .ctor` leaves. -/
private def throwMatch (code : UInt64) : Except Error (State × UInt64) :=
  if code = matchFull then .error .full
  else if code = matchSelfTrade then .error .selfTrade
  else if code = matchUnauthorized then .error .unauthorized
  else .error .overflow

def u64Max : UInt64 := ~~~(0 : UInt64)

def empty4 : Vector UInt64 4 := #v[0, 0, 0, 0]

def emptyEvents : Vector MarketEvent 5 :=
  #v[.uninitialized, .uninitialized, .uninitialized, .uninitialized, .uninitialized]

/-- 每个 instruction 覆盖上一批事件；旧 payload 无需清零，`eventCount` 决定有效前缀。 -/
private def beginEvents (s : State) : State :=
  { s with eventCount := 0, lastEvent := .uninitialized }

/-- Host accumulator 在保存前按 instruction 内顺序覆盖每个 wire event 的 u16 index。 -/
private def MarketEvent.withIndex (event : MarketEvent) (index : UInt64) : MarketEvent :=
  match event with
  | .uninitialized => .uninitialized
  | .header => .header
  | .fill _ maker0 maker1 maker2 maker3 sequence price filled remaining =>
      .fill index maker0 maker1 maker2 maker3 sequence price filled remaining
  | .place _ sequence clientLo clientHi price placed =>
      .place index sequence clientLo clientHi price placed
  | .reduce _ sequence price removed remaining =>
      .reduce index sequence price removed remaining
  | .evict _ maker0 maker1 maker2 maker3 sequence price evicted =>
      .evict index maker0 maker1 maker2 maker3 sequence price evicted
  | .fillSummary _ clientLo clientHi totalBase totalQuote totalFee =>
      .fillSummary index clientLo clientHi totalBase totalQuote totalFee
  | .fee _ fees => .fee index fees
  | .timeInForce _ sequence slot time => .timeInForce index sequence slot time
  | .expiredOrder _ maker0 maker1 maker2 maker3 sequence price removed =>
      .expiredOrder index maker0 maker1 maker2 maker3 sequence price removed

/--
写满后把 `matchError` 标成 `matchFull`，不丢事件假装成功。
调用点用当前 `eventCount` 构造 wire index。
不在这里二次 match event，因为动态 variant 已摊平成 State 的 tag/payload leaves。
-/
def appendEvent (s : State) (event : MarketEvent) : State :=
  if h : s.eventCount.toNat < 5 then
    { s with
      events := s.events.set s.eventCount.toNat event
      eventCount := s.eventCount + 1
      lastEvent := event }
  else
    { s with matchError := matchFull }

private def finishWithEvent (s : State) (event : MarketEvent) (ret : UInt64) :
    Except Error (State × UInt64) :=
  let next := appendEvent s event
  if next.matchError ≠ 0 then .error (errorOfMatch next.matchError)
  else .ok ({ next with matchStopped := 0, matchError := 0, matchLevel := 0 }, ret)

attribute [pf_inline] beginEvents MarketEvent.withIndex appendEvent
  finishWithEvent errorOfMatch throwMatch

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

/-- Signer lookup for take-only paths: unlike free-funds entries, a missing seat maps to sentinel max. -/
private def optionalTraderAddress (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error UInt64 :=
  if s.traderUsed[0]! ≠ 0 && s.traderKey0[0]! = key0 && s.traderKey1[0]! = key1 &&
      s.traderKey2[0]! = key2 && s.traderKey3[0]! = key3 then .ok 1
  else if s.traderUsed[1]! ≠ 0 && s.traderKey0[1]! = key0 && s.traderKey1[1]! = key1 &&
      s.traderKey2[1]! = key2 && s.traderKey3[1]! = key3 then .ok 2
  else if s.traderUsed[2]! ≠ 0 && s.traderKey0[2]! = key0 && s.traderKey1[2]! = key1 &&
      s.traderKey2[2]! = key2 && s.traderKey3[2]! = key3 then .ok 3
  else if s.traderUsed[3]! ≠ 0 && s.traderKey0[3]! = key0 && s.traderKey1[3]! = key1 &&
      s.traderKey2[3]! = key2 && s.traderKey3[3]! = key3 then .ok 4
  else .ok u64Max

attribute [pf_inline] optionalTraderAddress

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
  else .error .unauthorized

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
  if st.baseFree > u64Max - baseLots then
    .error .overflow
  else if st.quoteFree > u64Max - quoteLots then
    .error .overflow
  else if st.matchStopped ≠ (0 : UInt64) then
    let address := st.matchStopped
    let i := address.toNat - 1
    if h : i < 4 then
      if st.traderBaseFree[i]! ≤ u64Max - baseLots then
        if st.traderQuoteFree[i]! ≤ u64Max - quoteLots then
          .ok ({ st with
                  baseFree := st.baseFree + baseLots
                  quoteFree := st.quoteFree + quoteLots
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
                quoteFree := st.quoteFree + quoteLots
                baseFree := st.baseFree + baseLots
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
              quoteFree := st.quoteFree + quoteLots
              baseFree := st.baseFree + baseLots
              matchStopped := address }, address)
    else
      .error .overflow
  else
    .error .full

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
  if amount > s.baseFree then
    .error .overflow
  else
    .ok ({ s with
            baseFree := s.baseFree - amount
            traderBaseFree := s.traderBaseFree.set (i % 4) (available - amount) }, amount)

/-- Quote-lot 版本；单独入口避免把 base/quote 两种单位混进一个 UInt64 返回值。 -/
def withdrawQuoteFor (s : State) (key0 key1 key2 key3 requested : UInt64) :
    Except Error (State × UInt64) := do
  let address ← requireTraderAddress s key0 key1 key2 key3
  let i := address.toNat - 1
  let available := s.traderQuoteFree[i]!
  let amount := if requested < available then requested else available
  if amount > s.quoteFree then
    .error .overflow
  else
    .ok ({ s with
            quoteFree := s.quoteFree - amount
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

/-- Resolve a resting order's internal trader-tree address before constructing a wire event. -/
private def makerKey0 (s : State) (address : UInt64) : UInt64 :=
  if registeredSeat s address then s.traderKey0[address.toNat - 1]! else address

private def makerKey1 (s : State) (address : UInt64) : UInt64 :=
  if registeredSeat s address then s.traderKey1[address.toNat - 1]! else 0

private def makerKey2 (s : State) (address : UInt64) : UInt64 :=
  if registeredSeat s address then s.traderKey2[address.toNat - 1]! else 0

private def makerKey3 (s : State) (address : UInt64) : UInt64 :=
  if registeredSeat s address then s.traderKey3[address.toNat - 1]! else 0

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

attribute [pf_inline] registeredSeat makerKey0 makerKey1 makerKey2 makerKey3
  postAskFunds postBidFunds

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
              st := { st with matchError := matchFull }
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
              let maker := s.traders[3]!
              st := appendEvent st
                (.evict st.eventCount (makerKey0 s maker) (makerKey1 s maker)
                  (makerKey2 s maker) (makerKey3 s maker)
                  s.sequences[3]! s.priceTicks[3]! s.sizes[3]!)
      else if i = 15 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            st := appendEvent st
              (.place st.eventCount s.sequence clientOrderIdLo clientOrderIdHi price size)
      else if i = 16 then
        if st.matchStopped ≠ (0 : UInt64) then
          if st.matchError = (0 : UInt64) then
            if lastSlot ≠ 0 || lastTime ≠ 0 then
              st := appendEvent st (.timeInForce st.eventCount s.sequence lastSlot lastTime)
    if st.matchError ≠ 0 then
      .error (errorOfMatch st.matchError)
    else if st.matchStopped = 0 then
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
                st := { st with matchError := matchFull }
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
                let maker := s.bidTraders[3]!
                st := appendEvent st
                  (.evict st.eventCount (makerKey0 s maker) (makerKey1 s maker)
                    (makerKey2 s maker) (makerKey3 s maker)
                    (~~~s.bidSequences[3]!) s.bidPriceTicks[3]! s.bidSizes[3]!)
        else if i = 15 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              st := appendEvent st
                (.place st.eventCount s.sequence clientOrderIdLo clientOrderIdHi price size)
        else if i = 16 then
          if st.matchStopped ≠ (0 : UInt64) then
            if st.matchError = (0 : UInt64) then
              if lastSlot ≠ 0 || lastTime ≠ 0 then
                st := appendEvent st (.timeInForce st.eventCount s.sequence lastSlot lastTime)
      if st.matchError ≠ 0 then
        .error (errorOfMatch st.matchError)
      else if st.matchStopped = 0 then
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

/-- Unlock canceled or expired ask inventory in its maker's authoritative TraderState. -/
private def unlockAskTrader (s : State) (maker amount : UInt64) : State :=
  if registeredSeat s maker then
    let i := maker.toNat - 1
    if amount > s.traderBaseLocked[i]! then
      { s with matchStopped := 1, matchError := 1 }
    else if s.traderBaseFree[i]! > u64Max - amount then
      { s with matchStopped := 1, matchError := 1 }
    else
      { s with
        traderBaseLocked := s.traderBaseLocked.set (i % 4)
          (s.traderBaseLocked[i]! - amount)
        traderBaseFree := s.traderBaseFree.set (i % 4)
          (s.traderBaseFree[i]! + amount) }
  else
    s

/-- Settle one ask fill to its maker: base leaves locked and quote becomes free. -/
private def fillAskTrader
    (s : State) (maker baseAmount quoteAmount : UInt64) : State :=
  if registeredSeat s maker then
    let i := maker.toNat - 1
    if baseAmount > s.traderBaseLocked[i]! then
      { s with matchStopped := 1, matchError := 1 }
    else if s.traderQuoteFree[i]! > u64Max - quoteAmount then
      { s with matchStopped := 1, matchError := 1 }
    else
      { s with
        traderBaseLocked := s.traderBaseLocked.set (i % 4)
          (s.traderBaseLocked[i]! - baseAmount)
        traderQuoteFree := s.traderQuoteFree.set (i % 4)
          (s.traderQuoteFree[i]! + quoteAmount) }
  else
    s

/-- Unlock canceled or expired bid collateral in its maker's TraderState. -/
private def unlockBidTrader (s : State) (maker quoteAmount : UInt64) : State :=
  if registeredSeat s maker then
    let i := maker.toNat - 1
    if quoteAmount > s.traderQuoteLocked[i]! then
      { s with matchStopped := 1, matchError := 1 }
    else if s.traderQuoteFree[i]! > u64Max - quoteAmount then
      { s with matchStopped := 1, matchError := 1 }
    else
      { s with
        traderQuoteLocked := s.traderQuoteLocked.set (i % 4)
          (s.traderQuoteLocked[i]! - quoteAmount)
        traderQuoteFree := s.traderQuoteFree.set (i % 4)
          (s.traderQuoteFree[i]! + quoteAmount) }
  else
    s

/-- Settle one bid fill to its maker: quote leaves locked and base becomes free. -/
private def fillBidTrader
    (s : State) (maker quoteAmount baseAmount : UInt64) : State :=
  if registeredSeat s maker then
    let i := maker.toNat - 1
    if quoteAmount > s.traderQuoteLocked[i]! then
      { s with matchStopped := 1, matchError := 1 }
    else if s.traderBaseFree[i]! > u64Max - baseAmount then
      { s with matchStopped := 1, matchError := 1 }
    else
      { s with
        traderQuoteLocked := s.traderQuoteLocked.set (i % 4)
          (s.traderQuoteLocked[i]! - quoteAmount)
        traderBaseFree := s.traderBaseFree.set (i % 4)
          (s.traderBaseFree[i]! + baseAmount) }
  else
    s

attribute [pf_inline] unlockAskTrader fillAskTrader unlockBidTrader fillBidTrader

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

private def MatchAcc.pushEvent (acc : MatchAcc) (event : MarketEvent) : Except Error MatchAcc :=
  if h : acc.eventCount.toNat < 5 then
    let indexed := event.withIndex acc.eventCount
    .ok { acc with
      events := acc.events.set acc.eventCount.toNat indexed
      eventCount := acc.eventCount + 1
      lastEvent := indexed }
  else
    .error .full

/--
沿 ask 树中序投影做至多四档的 IOC。过期单取消并继续；第一档超限即停止；
整档成交继续，部分成交终止。所有乘加都在 UInt64 剖面内 fail-closed。
-/
private def scanAsks (s : State) (taker limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior)
    (fuel i : Nat) (acc : MatchAcc) : Except Error MatchAcc :=
  match fuel with
  | 0 => .ok acc
  | fuel' + 1 => do
    if acc.stopped || acc.filledBase = acc.targetBase then
      .ok acc
    else if h : i < 4 then
      let size := acc.sizes[i]
      if size = 0 then
        scanAsks s taker limit nowSlot nowTime behavior fuel' (i + 1) acc
      else if expired s.lastSlots[i] s.lastTimes[i] nowSlot nowTime then
        if acc.expiredBase ≤ u64Max - size then
          let maker := s.traders[i]
          let next ← acc.pushEvent
            (.expiredOrder 0 (makerKey0 s maker) (makerKey1 s maker)
              (makerKey2 s maker) (makerKey3 s maker)
              s.sequences[i] s.priceTicks[i] size)
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
        | .abort => .error .selfTrade
        | .cancelProvide =>
          if acc.expiredBase ≤ u64Max - size then
            let next ← acc.pushEvent (.reduce 0 s.sequences[i] s.priceTicks[i] size 0)
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
            let next ← acc.pushEvent
              (.reduce 0 s.sequences[i] s.priceTicks[i] reduced (size - reduced))
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
              let maker := s.traders[i]
              let next ← acc.pushEvent
                (.fill 0 (makerKey0 s maker) (makerKey1 s maker)
                  (makerKey2 s maker) (makerKey3 s maker)
                  s.sequences[i] price fill (size - fill))
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

/-- Replay the bounded host event prefix into authoritative ask-maker seat balances. -/
private def applyAskEvents
    (s : State) (taker count : UInt64) (fuel i : Nat) : State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s.matchError ≠ 0 || count.toNat ≤ i then s
    else if h : i < 5 then
      let next :=
        match s.events[i] with
        | .expiredOrder _ maker0 maker1 maker2 maker3 _ _ removed =>
          let maker := traderAddressFor s maker0 maker1 maker2 maker3
          unlockAskTrader s maker removed
        | .reduce _ _ _ removed _ => unlockAskTrader s taker removed
        | .fill _ maker0 maker1 maker2 maker3 _ price filled _ =>
          let maker := traderAddressFor s maker0 maker1 maker2 maker3
          if s.baseLotsPerBaseUnit = 0 then
            { s with matchStopped := 1, matchError := 1 }
          else if price = 0 || s.tickSize = 0 then
            fillAskTrader s maker filled 0
          else
            match adjustedQuoteFor s price filled with
            | .error _ => { s with matchStopped := 1, matchError := 1 }
            | .ok adjusted =>
              let makerQuote := adjusted / s.baseLotsPerBaseUnit
              if s.matchMakerQuote > u64Max - makerQuote then
                { s with matchStopped := 1, matchError := 1 }
              else
                let ledger := fillAskTrader s maker filled makerQuote
                { ledger with matchMakerQuote := s.matchMakerQuote + makerQuote }
        | _ => s
      applyAskEvents next taker count fuel' (i + 1)
    else
      s

/-- Debit a registered free-funds buy taker's quote and credit received base, then project totals. -/
private def commitBuy
    (s : State) (taker filled expired quoteLots feeLots : UInt64) :
    Except Error (State × UInt64) :=
  if quoteLots > u64Max - feeLots then
    .error .overflow
  else
    let quoteDebit := quoteLots + feeLots
    if filled > u64Max - expired then
      .error .overflow
    else
      let baseDebit := filled + expired
      if baseDebit > s.baseLocked then
        .error .overflow
      else if s.baseFree > u64Max - baseDebit then
        .error .overflow
      else if s.unclaimedFees > u64Max - feeLots then
        .error .overflow
      else if registeredSeat s taker then
        let i := taker.toNat - 1
        if quoteDebit > s.traderQuoteFree[i]! then
          .error .overflow
        else if s.traderBaseFree[i]! > u64Max - filled then
          .error .overflow
        else if quoteDebit > s.quoteFree then
          .error .overflow
        else
          let remainingQuoteFree := s.quoteFree - quoteDebit
          if remainingQuoteFree > u64Max - s.matchMakerQuote then
            .error .overflow
          else
            .ok ({ s with
              traderQuoteFree := s.traderQuoteFree.set (i % 4)
                (s.traderQuoteFree[i]! - quoteDebit)
              traderBaseFree := s.traderBaseFree.set (i % 4)
                (s.traderBaseFree[i]! + filled)
              quoteFree := remainingQuoteFree + s.matchMakerQuote
              baseLocked := s.baseLocked - baseDebit
              baseFree := s.baseFree + baseDebit
              unclaimedFees := s.unclaimedFees + feeLots }, filled)
      else
        if quoteDebit > s.quoteLocked then
          .error .overflow
        else if s.quoteFree > u64Max - quoteLots then
          .error .overflow
        else if filled = 0 then
          .ok ({ s with
            quoteLocked := s.quoteLocked - quoteDebit
            quoteFree := s.quoteFree + quoteLots
            baseLocked := s.baseLocked - baseDebit
            baseFree := s.baseFree + baseDebit
            unclaimedFees := s.unclaimedFees + feeLots }, filled)
        else
          let _ := tokenTransferChecked filled 6
          .ok ({ s with
            quoteLocked := s.quoteLocked - quoteDebit
            quoteFree := s.quoteFree + quoteLots
            baseLocked := s.baseLocked - baseDebit
            baseFree := s.baseFree + baseDebit
            unclaimedFees := s.unclaimedFees + feeLots }, filled)

attribute [pf_inline] commitBuy

/--
把聚合撮合结果结算到摊平 TraderState。注册 maker 的逐档余额先按 event replay
更新，注册 taker 的 quote-free / base-free 在 commit 中原子更新。

registered free-funds buy 从 taker 的 `quoteFree` 扣成交额和费用，并把成交 base
加进该 seat 的 `baseFree`。未注册 take-only 暂走 aggregate compatibility 分支，
其双 vault 输入/输出仍由 adapter 后续补齐。四个 aggregate 余额始终同步投影所有
seat；撮合只增加 `unclaimedFees`，`collectedFees` 留给独立收取动作。
-/
private def settleBuy (s : State) (taker clientOrderIdLo clientOrderIdHi : UInt64)
    (acc : MatchAcc) : Except Error (State × UInt64) :=
  if s.baseLotsPerBaseUnit = 0 then
    .error .overflow
  else if acc.adjustedQuote ≠ 0 && s.takerFeeBps > u64Max / acc.adjustedQuote then
    .error .overflow
  else
    let quoteLots := ceilDiv acc.adjustedQuote s.baseLotsPerBaseUnit
    let adjustedFee := ceilDiv (acc.adjustedQuote * s.takerFeeBps) 10000
    let feeLots := ceilDiv adjustedFee s.baseLotsPerBaseUnit
    let ledgerStart := { s with
      sizes := acc.sizes
      events := acc.events
      eventCount := acc.eventCount
      lastEvent := acc.lastEvent
      matchMakerQuote := 0
      matchStopped := 0
      matchError := 0 }
    let ledger := applyAskEvents ledgerStart taker acc.eventCount 5 0
    if ledger.matchError ≠ 0 then
      .error (errorOfMatch ledger.matchError)
    else do
      let (settled, filled) ←
        commitBuy ledger taker acc.filledBase acc.expiredBase quoteLots feeLots
      finishWithEvent settled
        (.fillSummary settled.eventCount clientOrderIdLo clientOrderIdHi
          filled quoteLots feeLots) filled

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
  settleBuy s taker clientOrderIdLo clientOrderIdHi acc

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

private def SellAcc.pushEvent (acc : SellAcc) (event : MarketEvent) : Except Error SellAcc :=
  if h : acc.eventCount.toNat < 5 then
    let indexed := event.withIndex acc.eventCount
    .ok { acc with
      events := acc.events.set acc.eventCount.toNat indexed
      eventCount := acc.eventCount + 1
      lastEvent := indexed }
  else
    .error .full

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
          let maker := s.bidTraders[i]
          let next ← acc.pushEvent
            (.expiredOrder 0 (makerKey0 s maker) (makerKey1 s maker)
              (makerKey2 s maker) (makerKey3 s maker)
              (~~~s.bidSequences[i]) s.bidPriceTicks[i] size)
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
        | .abort => .error .selfTrade
        | .cancelProvide =>
          let unlocked ← bidCollateral s s.bidPriceTicks[i] size
          if acc.unlockedQuote ≤ u64Max - unlocked then
            let next ← acc.pushEvent
              (.reduce 0 (~~~s.bidSequences[i]) s.bidPriceTicks[i] size 0)
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
            let next ← acc.pushEvent
              (.reduce 0 (~~~s.bidSequences[i]) s.bidPriceTicks[i] reduced (size - reduced))
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
          let maker := s.bidTraders[i]
          let next ← acc.pushEvent
            (.fill 0 (makerKey0 s maker) (makerKey1 s maker)
              (makerKey2 s maker) (makerKey3 s maker)
              (~~~s.bidSequences[i]) s.bidPriceTicks[i] fill (size - fill))
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

/-- Replay the bounded host event prefix into authoritative bid-maker seat balances. -/
private def applySellEvents
    (s : State) (taker count : UInt64) (fuel i : Nat) : State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s.matchError ≠ 0 || count.toNat ≤ i then s
    else if h : i < 5 then
      let next :=
        match s.events[i] with
        | .expiredOrder _ maker0 maker1 maker2 maker3 _ price removed =>
          let maker := traderAddressFor s maker0 maker1 maker2 maker3
          match bidCollateral s price removed with
          | .ok quote => unlockBidTrader s maker quote
          | .error _ => { s with matchStopped := 1, matchError := 1 }
        | .reduce _ _ price removed _ =>
          match bidCollateral s price removed with
          | .ok quote => unlockBidTrader s taker quote
          | .error _ => { s with matchStopped := 1, matchError := 1 }
        | .fill _ maker0 maker1 maker2 maker3 _ price filled _ =>
          let maker := traderAddressFor s maker0 maker1 maker2 maker3
          match bidCollateral s price filled with
          | .ok quote => fillBidTrader s maker quote filled
          | .error _ => { s with matchStopped := 1, matchError := 1 }
        | _ => s
      applySellEvents next taker count fuel' (i + 1)
    else
      s

/-- Debit the registered sell taker's free base and credit net quote, then project totals. -/
private def commitSell
    (s : State) (taker filled unlocked makerQuote grossQuote feeLots : UInt64) :
    Except Error (State × UInt64) :=
  if grossQuote < feeLots then
    .error .overflow
  else if makerQuote > u64Max - unlocked then
    .error .overflow
  else
    let quoteDebit := makerQuote + unlocked
    let takerQuote := grossQuote - feeLots
    if quoteDebit > s.quoteLocked || filled > s.baseFree then
      .error .overflow
    else if takerQuote > u64Max - unlocked then
      .error .overflow
    else
      let quoteCredit := takerQuote + unlocked
      if s.quoteFree > u64Max - quoteCredit then
        .error .overflow
      else if s.unclaimedFees > u64Max - feeLots then
        .error .overflow
      else if registeredSeat s taker then
        let i := taker.toNat - 1
        if filled > s.traderBaseFree[i]! then
          .error .overflow
        else if s.traderQuoteFree[i]! > u64Max - takerQuote then
          .error .overflow
        else
          .ok ({ s with
            traderBaseFree := s.traderBaseFree.set (i % 4)
              (s.traderBaseFree[i]! - filled)
            traderQuoteFree := s.traderQuoteFree.set (i % 4)
              (s.traderQuoteFree[i]! + takerQuote)
            quoteLocked := s.quoteLocked - quoteDebit
            quoteFree := s.quoteFree + quoteCredit
            unclaimedFees := s.unclaimedFees + feeLots }, filled)
      else if filled = 0 then
        .ok ({ s with
          quoteLocked := s.quoteLocked - quoteDebit
          quoteFree := s.quoteFree + quoteCredit
          unclaimedFees := s.unclaimedFees + feeLots }, filled)
      else
        let _ := tokenTransferChecked filled 6
        .ok ({ s with
          quoteLocked := s.quoteLocked - quoteDebit
          quoteFree := s.quoteFree + quoteCredit
          unclaimedFees := s.unclaimedFees + feeLots }, filled)

attribute [pf_inline] commitSell

private def settleSell (s : State) (taker clientOrderIdLo clientOrderIdHi : UInt64)
    (acc : SellAcc) : Except Error (State × UInt64) :=
  if s.baseLotsPerBaseUnit = 0 then
    .error .overflow
  else if acc.adjustedQuote ≠ 0 && s.takerFeeBps > u64Max / acc.adjustedQuote then
    .error .overflow
  else
    let grossQuote := acc.adjustedQuote / s.baseLotsPerBaseUnit
    let adjustedFee := ceilDiv (acc.adjustedQuote * s.takerFeeBps) 10000
    let feeLots := ceilDiv adjustedFee s.baseLotsPerBaseUnit
    let ledgerStart := { s with
      bidSizes := acc.sizes
      events := acc.events
      eventCount := acc.eventCount
      lastEvent := acc.lastEvent
      matchStopped := 0
      matchError := 0 }
    let ledger := applySellEvents ledgerStart taker acc.eventCount 5 0
    if ledger.matchError ≠ 0 then
      .error (errorOfMatch ledger.matchError)
    else do
      let (settled, filled) ← commitSell ledger taker acc.filledBase acc.unlockedQuote
        acc.makerQuote grossQuote feeLots
      finishWithEvent settled
        (.fillSummary settled.eventCount clientOrderIdLo clientOrderIdHi
          filled grossQuote feeLots) filled

/-- 可测试的 N=4 sell IOC 宿主语义。 -/
def swapSellForClientAt (s : State)
    (taker clientOrderIdLo clientOrderIdHi want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) : Except Error (State × UInt64) := do
  let s := beginEvents s
  let acc ← scanBids s taker limit nowSlot nowTime behavior 4 0
    { sizes := s.bidSizes, targetBase := want, filledBase := 0, adjustedQuote := 0,
      makerQuote := 0, unlockedQuote := 0, stopped := false, events := s.events,
      eventCount := s.eventCount, lastEvent := s.lastEvent }
  settleSell s taker clientOrderIdLo clientOrderIdHi acc

/-- 兼容宿主调用：client order id 为零。 -/
def swapSellForAt (s : State) (taker want limit nowSlot nowTime : UInt64)
    (behavior : SelfTradeBehavior) : Except Error (State × UInt64) :=
  swapSellForClientAt s taker 0 0 want limit nowSlot nowTime behavior

def swapSellAt (s : State) (want limit nowSlot nowTime : UInt64) :
    Except Error (State × UInt64) :=
  swapSellForAt s u64Max want limit nowSlot nowTime .abort

/-- Ask-fold cancellation/expiry: update the book accumulator and its maker seat together. -/
private def unlockAskFold (s : State) (j : Nat) (amount : UInt64) : State :=
  let size := s.sizes[j]!
  if size < amount then
    { s with matchStopped := 1, matchError := 1 }
  else if s.matchExpired > u64Max - amount then
    { s with matchStopped := 1, matchError := 1 }
  else
    let ledger := unlockAskTrader s s.traders[j]! amount
    { ledger with
      sizes := s.sizes.set (j % 4) (size - amount)
      matchExpired := s.matchExpired + amount }

/-- Ask-fold fill: update its maker seat and all quote/base accumulators in one transition. -/
private def fillAskFold (s : State) (j : Nat) (fill : UInt64) : State :=
  let size := s.sizes[j]!
  let price := s.priceTicks[j]!
  if size < fill then
    { s with matchStopped := 1, matchError := 1 }
  else if s.baseLotsPerBaseUnit = 0 then
    { s with matchStopped := 1, matchError := 1 }
  else if price ≠ 0 && s.tickSize > u64Max / price then
    { s with matchStopped := 1, matchError := 1 }
  else
    let quotePerBase := price * s.tickSize
    if quotePerBase ≠ 0 && fill > u64Max / quotePerBase then
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
        let ledger := fillAskTrader s s.traders[j]! fill makerQuote
        { ledger with
          sizes := s.sizes.set (j % 4) (size - fill)
          matchFilled := s.matchFilled + fill
          matchQuote := s.matchQuote + adjusted
          matchMakerQuote := s.matchMakerQuote + makerQuote }

private def finishFold (s : State) (taker quoteLots feeLots : UInt64) :
    Except Error (State × UInt64) :=
  commitBuy s taker s.matchFilled s.matchExpired quoteLots feeLots

private def settleFold (s : State) (taker : UInt64) : Except Error (State × UInt64) :=
  if s.matchError ≠ 0 then throwMatch s.matchError
  else finishFold s taker s.matchQuote s.matchLimit

attribute [pf_inline] unlockAskFold fillAskFold finishFold settleFold

/--
链上 N=4 IOC。`behavior`：0=Abort、1=CancelProvide、2=DecrementTake。
十九次 state-carrying bounded fold：第 0 次清瞬时响应，接着十六次按四档 ×
（slot TIF、time TIF、撮合、advance）推进，第 17 次计算结算数值，第 18 次追加
summary。把算术和动态 event write 分 phase，避免 checked-arithmetic continuation
复制动态 variant-vector write；循环 store 会继续下一次，不再静态复制后续档位。
-/
private def swapBuyFold (s : State)
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
          st := { st with matchQuote := 0, matchLimit := 0 }
        else
          let quoteLots := (st.matchQuote - 1) / st.baseLotsPerBaseUnit + 1
          if st.takerFeeBps = 0 then
            st := { st with matchQuote := quoteLots, matchLimit := 0 }
          else if st.takerFeeBps ≤ u64Max / st.matchQuote then
            let feeProduct := st.matchQuote * st.takerFeeBps
            let adjustedFee := (feeProduct - 1) / 10000 + 1
            let feeLots := (adjustedFee - 1) / st.baseLotsPerBaseUnit + 1
            st := { st with matchQuote := quoteLots, matchLimit := feeLots }
          else
            st := { st with matchError := 1 }
    else if i = 18 then
      if st.matchError = 0 then
        st := appendEvent st
          (.fillSummary st.eventCount clientOrderIdLo clientOrderIdHi
            st.matchFilled st.matchQuote st.matchLimit)
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
              let unlocked := unlockAskFold st j size
              let maker := st.traders[j]!
              st := appendEvent unlocked
                (.expiredOrder st.eventCount (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  st.sequences[j]! st.priceTicks[j]! size)
        else if phase = 1 then
          if st.lastTimes[j]! ≠ 0 then
            if st.lastTimes[j]! < unixTime then
              let unlocked := unlockAskFold st j size
              let maker := st.traders[j]!
              st := appendEvent unlocked
                (.expiredOrder st.eventCount (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  st.sequences[j]! st.priceTicks[j]! size)
        else if phase = 2 then
          if st.matchLimit < st.priceTicks[j]! then
            st := { st with matchStopped := 1 }
          else if st.traders[j]! ≠ taker then
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let filled := fillAskFold st j remaining
              let maker := st.traders[j]!
              st := appendEvent { filled with matchStopped := 1 }
                (.fill st.eventCount (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  st.sequences[j]! st.priceTicks[j]! remaining (size - remaining))
            else
              let filled := fillAskFold st j size
              let maker := st.traders[j]!
              st := appendEvent filled
                (.fill st.eventCount (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  st.sequences[j]! st.priceTicks[j]! size 0)
          else if behavior = 0 then
            st := { st with matchStopped := 1, matchError := matchSelfTrade }
          else if behavior = 1 then
            let unlocked := unlockAskFold st j size
            st := appendEvent unlocked
              (.reduce st.eventCount st.sequences[j]! st.priceTicks[j]! size 0)
          else if behavior = 2 then
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let unlocked := unlockAskFold st j remaining
              st := appendEvent
                { unlocked with
                  matchWant := st.matchWant - remaining
                  matchStopped := 1 }
                (.reduce st.eventCount st.sequences[j]! st.priceTicks[j]!
                  remaining (size - remaining))
            else
              let unlocked := unlockAskFold st j size
              st := appendEvent { unlocked with matchWant := st.matchWant - size }
                (.reduce st.eventCount st.sequences[j]! st.priceTicks[j]! size 0)
          else
            st := { st with matchStopped := 1, matchError := 1 }
  settleFold st taker

attribute [pf_inline] swapBuyFold

/-- SVM take-only/free-funds adapter; self-trade identity always comes from account 1 signer. -/
@[pf_entry]
def swapBuy (s : State)
    (behavior clientOrderIdLo clientOrderIdHi want limit : UInt64) :
    Except Error (State × UInt64) := do
  let taker ← optionalTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  swapBuyFold s taker behavior clientOrderIdLo clientOrderIdHi want limit

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
        let ledger := unlockBidTrader s s.bidTraders[j]! unlocked
        { ledger with
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
        let ledger := fillBidTrader s s.bidTraders[j]! makerQuote fill
        { ledger with
          bidSizes := s.bidSizes.set (j % 4) (size - fill)
          matchFilled := s.matchFilled + fill
          matchQuote := s.matchQuote + adjusted
          matchMakerQuote := s.matchMakerQuote + makerQuote }
  else
    { s with matchStopped := 1, matchError := 1 }

attribute [pf_inline] unlockBidFold fillBidFold

private def commitSellFold (s : State) (taker grossQuote feeLots : UInt64) :
    Except Error (State × UInt64) :=
  commitSell s taker s.matchFilled s.matchExpired s.matchMakerQuote grossQuote feeLots

private def settleSellFold (s : State) (taker : UInt64) : Except Error (State × UInt64) :=
  if s.matchError ≠ 0 then throwMatch s.matchError
  else commitSellFold s taker s.matchLimit s.matchWant

attribute [pf_inline] commitSellFold settleSellFold

/--
链上 N=4 sell IOC。与 buy 一样使用十九次 state-carrying bounded fold：第 0 次
清瞬时响应，接着十六次按四档 ×（slot TIF、time TIF、撮合、advance）推进，
第 17 次计算结算数值，第 18 次追加 summary。内联 State helper 的结果可直接接
typed event 动态写，不再借 `lastEvent` 跨 phase 暂存完整 variant。
-/
private def swapSellFold (s : State)
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
    else if i = 18 then
      if st.matchError = 0 then
        st := appendEvent st
          (.fillSummary st.eventCount clientOrderIdLo clientOrderIdHi
            st.matchFilled st.matchLimit st.matchWant)
    else if st.matchStopped = 0 then
      let k := i - 1
      let phase := k % 4
      let j := st.matchLevel.toNat
      let size := st.bidSizes[j]!
      if st.matchFilled = st.matchWant then
        st := { st with matchStopped := 1 }
      else if phase = 3 then
        st := { st with matchLevel := st.matchLevel + 1 }
      else if size ≠ 0 then
        if phase = 0 then
          if st.bidLastSlots[j]! ≠ 0 then
            if st.bidLastSlots[j]! < clockSlot then
              let unlocked := unlockBidFold st j size
              let maker := st.bidTraders[j]!
              st := appendEvent unlocked
                (.expiredOrder st.eventCount
                  (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size)
        else if phase = 1 then
          if st.bidLastTimes[j]! ≠ 0 then
            if st.bidLastTimes[j]! < unixTime then
              let unlocked := unlockBidFold st j size
              let maker := st.bidTraders[j]!
              st := appendEvent unlocked
                (.expiredOrder st.eventCount
                  (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size)
        else if phase = 2 then
          if st.bidPriceTicks[j]! < st.matchLimit then
            st := { st with matchStopped := 1 }
          else if st.bidTraders[j]! ≠ taker then
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let filled := fillBidFold st j remaining
              let maker := st.bidTraders[j]!
              st := appendEvent { filled with matchStopped := 1 }
                (.fill st.eventCount
                  (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! remaining (size - remaining))
            else
              let filled := fillBidFold st j size
              let maker := st.bidTraders[j]!
              st := appendEvent filled
                (.fill st.eventCount
                  (makerKey0 st maker) (makerKey1 st maker)
                  (makerKey2 st maker) (makerKey3 st maker)
                  (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size 0)
          else if behavior = 0 then
            st := { st with matchStopped := 1, matchError := matchSelfTrade }
          else if behavior = 1 then
            let unlocked := unlockBidFold st j size
            st := appendEvent unlocked
              (.reduce st.eventCount
                (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size 0)
          else if behavior = 2 then
            let remaining := st.matchWant - st.matchFilled
            if remaining ≤ size then
              let unlocked := unlockBidFold st j remaining
              st := appendEvent
                { unlocked with
                  matchWant := st.matchWant - remaining
                  matchStopped := 1 }
                (.reduce st.eventCount (~~~st.bidSequences[j]!) st.bidPriceTicks[j]!
                  remaining (size - remaining))
            else
              let unlocked := unlockBidFold st j size
              st := appendEvent { unlocked with matchWant := st.matchWant - size }
                (.reduce st.eventCount
                  (~~~st.bidSequences[j]!) st.bidPriceTicks[j]! size 0)
          else
            st := { st with matchStopped := 1, matchError := 1 }
  settleSellFold st taker

attribute [pf_inline] swapSellFold

/-- Bid-side SVM adapter with signer-derived self-trade identity. -/
@[pf_entry]
def swapSell (s : State)
    (behavior clientOrderIdLo clientOrderIdHi want limit : UInt64) :
    Except Error (State × UInt64) := do
  let taker ← optionalTraderAddress s (signerKey 1) (accKeyWord 1 1)
    (accKeyWord 1 2) (accKeyWord 1 3)
  swapSellFold s taker behavior clientOrderIdLo clientOrderIdHi want limit

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
                            st := appendEvent reduced
                              (.reduce reduced.eventCount sequence price removed (size - removed))
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
          .error (errorOfMatch st.matchError)
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
                    st := appendEvent reduced
                      (.reduce reduced.eventCount sequence price removed (size - removed))
                  else
                    st := { st with matchStopped := 1, matchError := 1 }
        if st.matchError ≠ 0 then
          .error (errorOfMatch st.matchError)
        else if st.matchExpired > st.quoteLocked then
          .error .overflow
        else if st.quoteFree > u64Max - st.matchExpired then
          .error .overflow
        else
          let reduced := st.matchFilled
          .ok ({ st with
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
    let fees := s.unclaimedFees
    let s := beginEvents s
    let settled := { s with
      collectedFees := s.collectedFees + fees
      unclaimedFees := 0 }
    .ok (appendEvent settled (.fee settled.eventCount fees), fees)
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
  | .header => 1
  | .fill _ _ _ _ _ _ _ _ _ => 2
  | .place _ _ _ _ _ _ => 3
  | .reduce _ _ _ _ _ => 4
  | .evict _ _ _ _ _ _ _ _ => 5
  | .fillSummary _ _ _ _ _ _ => 6
  | .fee _ _ => 7
  | .timeInForce _ _ _ _ => 8
  | .expiredOrder _ _ _ _ _ _ _ _ => 9

@[pf_entry]
def lastEventAmount (s : State) : UInt64 :=
  match s.lastEvent with
  | .uninitialized => 0
  | .header => 0
  | .fill _ _ _ _ _ _ _ filled _ => filled
  | .place _ _ _ _ _ placed => placed
  | .reduce _ _ _ removed _ => removed
  | .evict _ _ _ _ _ _ _ evicted => evicted
  | .fillSummary _ _ _ totalBase _ _ => totalBase
  | .fee _ fees => fees
  | .timeInForce _ _ lastValidSlot _ => lastValidSlot
  | .expiredOrder _ _ _ _ _ _ _ removed => removed

end Projects.Phoenix
