# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) `src/state` 摊进当前 SVM 剖面。抽出器不认嵌套 structure / 红黑树，所以官方 *记录* 摊成平行 `UInt64` 向量，不是自己发明的 6 槽。

## 官方 `src/state` 对上了什么

| 官方类型 | 本仓槽 |
|---|---|
| `FIFOMarket.base_lots_per_base_unit` | `baseLotsPerBaseUnit` |
| `tick_size_in_quote_lots_per_base_unit` | `tickSize` |
| `order_sequence_number` | `sequence` |
| `taker_fee_bps` / collected / unclaimed | `takerFeeBps` / `collectedFees` / `unclaimedFees` |
| `FIFOOrderId` × 4 | `priceTicks` / `sequences` |
| `FIFORestingOrder` × 4 | `traders` / `sizes` / `lastSlots` / `lastTimes` |
| `TraderState` | `quoteLocked` / `quoteFree` / `baseLocked` / `baseFree` |
| `Side` / `SelfTradeBehavior` | 无 payload 枚举（宿主） |
| TIF 哨兵 0 | `expired` |

34 个 u64 槽。`#pf_build Projects.Phoenix` digest `28a047016bb7ac90`。

当前链上 `swapBuy` 是 level-0 IOC 切片：检查限价和 time TIF，按
`min(want, sizes[0])` 部分或全部成交，保留 Token `TransferChecked` CPI，随后显式写回
`sizes_0` 和 `baseFree`。`swapBuyAt` 是宿主侧可测试语义，额外覆盖 slot TIF。

`postAsk` 链上入口仍只写 `sizes`；`postAskFull` 在宿主写价、序号、锁仓。费用可按账户
`takerFeeBps` 用 `feeOfBps` 计算，但当前成交入口还没有 collected/unclaimed fee 记账。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| `RedBlackTree` bids/asks/traders | 节点布局已在 `Examples.Tree`；Phoenix 书还没换成 `Vector Node` |
| `_padding: [u64; 32]` | 不进账户 |
| `OrderPacket.client_order_id: u128` | 只有 `UInt64` |
| `MarketEvent` 带 payload | 多构造子 inductive |
| `Ladder` / `Vec` | 不定长 |
| 跨档扫描 / Cancel 进链上 | 当前成交只处理档 0；尚未接红黑树或循环扫书 |
| slot TIF 进链上 | `swapBuyAt` 已覆盖；链上 `swapBuy` 当前只读 Clock unix time |
| 成交费用状态记账 | 只有 UInt64 bps 计算，还没更新 collected/unclaimed fee |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| `Log` self-CPI | 变长 event batch |

缺哪块再补 SVM，不要先假装全量兼容。
