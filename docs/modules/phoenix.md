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

34 个 u64 槽。`#pf_build Projects.Phoenix` digest `4603a8e42f8e7143`。

链上入口仍只改 `sizes` / `baseFree`：一次写多叶抽不出来。`postAskFull` 在宿主写价、序号、锁仓。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| `RedBlackTree` bids/asks/traders | 不定长树；不是 `Vector` |
| `_padding: [u64; 32]` | 不进账户 |
| `OrderPacket.client_order_id: u128` | 只有 `UInt64` |
| `MarketEvent` 带 payload | 多构造子 inductive |
| `Ladder` / `Vec` | 不定长 |
| 跨档部分成交 / Cancel 进链上 | `forBody` / `set 0 0` 抽出还坏 |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| `Log` self-CPI | 变长 event batch |

缺哪块再补 SVM，不要先假装全量兼容。
