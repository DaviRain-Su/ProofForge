# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) 的 ask-side IOC
语义放进当前 SVM 剖面。官方记录摊成平行 `UInt64` 向量；固定 N=4 的
`RBTree4` 保存规范红黑拓扑及中序次序的 refinement witness，但链上账户不复制
颜色和指针。

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
| `MatchingEngineResponse` | `match*` bounded-fold scratch |
| TIF 哨兵 0 | `expired`（严格 `<`；等于 deadline 仍有效） |

42 个 u64 槽。`#pf_build Projects.Phoenix` digest `b768c4809cea96c1`。

`swapBuyAt` 是完整的 bounded N=4 宿主语义；链上 `swapBuy` 用 17-phase
state-carrying fold 实现相同扫描：reset 后，每档依次检查 slot TIF、time TIF、
撮合并推进档位。过期单清零、解锁 base 并继续；第一个超限有效价格停止；整档
成交继续，部分成交停止。无流动性或超限 IOC 成功返回 0，不伪装成 overflow。

quote 和费用先按整次撮合聚合再向上取整。结算扣 `quoteLocked`、增加
`quoteFree`，扣 maker `baseLocked`，把成交和过期解锁量加到 `baseFree`，并增加
`unclaimedFees`；`collectedFees` 只由后续收费动作改变。非零成交保留 Token
`TransferChecked` CPI。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| 动态 `RedBlackTree` allocator / 插删旋转 | 当前只证明固定四节点规范拓扑和中序投影 |
| `_padding: [u64; 32]` | 不进账户 |
| `OrderPacket.client_order_id: u128` | 只有 `UInt64` |
| `MarketEvent` 带 payload | 多构造子 inductive |
| `Ladder` / `Vec` | 不定长 |
| bid book / trader tree / 动态 maker 身份 | 当前只做聚合 ask-side N=4 |
| self-trade / seat lifecycle / event batch | 需要更完整账户与事件模型 |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| `Log` self-CPI | 变长 event batch |

这是完整的 bounded N=4 Phoenix IOC 模型，不是完整 Phoenix-v1 动态账户实现。
