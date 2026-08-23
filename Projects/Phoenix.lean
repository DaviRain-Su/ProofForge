import ProofForge

/-!
Phoenix v1 `src/state` 在本仓剖面下的摊平。

官方 `FIFOMarket` 是三棵红黑树 + 泛型 trader key。抽出器不认嵌套
structure / 不定长树，所以这里把官方 *记录* 摊成平行 `UInt64` 向量：

  FIFOOrderId          → priceTicks / sequences
  FIFORestingOrder     → traders / sizes / lastSlots / lastTimes
  TraderState          → quoteLocked / quoteFree / baseLocked / baseFree
  MatchingEngineResponse 不作账户槽（瞬时）
  OrderPacket.client_order_id u128、红黑树、MarketEvent 仍关

N=4。档 0 是最优 ask。没有 bid 书。
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
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

def empty4 : Vector UInt64 4 := #v[0, 0, 0, 0]

/-- 官方 taker fee 默认常用 5 bps。不是 u128 上取整。 -/
def defaultFeeBps : UInt64 := 5

def feeOf (qty : UInt64) : UInt64 :=
  qty * defaultFeeBps / 10000

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
    baseFree := 0 }

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

/--
IOC 买：只打档 0。官方不会跳档。
`want ≤ sizes[0]` 才成交。成交把 maker 的 `baseLocked` 转成 taker `baseFree`。
-/
@[pf_entry]
def swapBuy (s : State) (want : UInt64) : Except Error (State × UInt64) :=
  if s.baseFree ≤ u64Max - want then
    if want ≤ s.sizes[0]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 0 (s.sizes[0]! - want)
              baseFree := s.baseFree + want }, want)
    else
      .error .overflow
  else
    .error .overflow

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
  if qty = 0 then 0 else qty * defaultFeeBps / 10000

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
