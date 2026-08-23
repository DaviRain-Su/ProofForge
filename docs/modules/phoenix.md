# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) 的双边 IOC
语义放进当前 SVM 剖面。官方记录摊成平行 `UInt64` 向量；每边固定 N=4 的
`RBTree4` 保存规范红黑拓扑及中序次序的 refinement witness，但链上账户不复制
颜色和指针。

## 官方 `src/state` 对上了什么

| 官方类型 | 本仓槽 |
|---|---|
| `FIFOMarket.base_lots_per_base_unit` | `baseLotsPerBaseUnit` |
| `tick_size_in_quote_lots_per_base_unit` | `tickSize` |
| `order_sequence_number` | `sequence` |
| `taker_fee_bps` / collected / unclaimed | `takerFeeBps` / `collectedFees` / `unclaimedFees` |
| ask `FIFOOrderId` / order × 4 | `priceTicks` / `sequences` / `traders` / `sizes` / TIF |
| bid `FIFOOrderId` / order × 4 | 对应的 `bid*` 平行向量 |
| `TraderState` | `quoteLocked` / `quoteFree` / `baseLocked` / `baseFree` |
| `Side` / `SelfTradeBehavior` | 无 payload 枚举（宿主） |
| `MatchingEngineResponse` | `match*` bounded-fold scratch |
| `MarketEvent` | tag + 五个规范 payload 槽；instruction 内固定容量 5 的 batch |
| TIF 哨兵 0 | `expired`（严格 `<`；等于 deadline 仍有效） |

104 个 8-byte 叶，账户含 discriminator 共 840 bytes。`#pf_build Projects.Phoenix`
digest `398e5164a731dc0`。

`postAsk` 是链上 free-funds 挂单：检查 incoming TIF 和 sequence 上界，锁定
`baseFree → baseLocked`，按 `(price, sequence)` 插入有序投影；书满时只有更低价
ask 能驱逐最差订单。物理空洞通过 bounded compare/swap 收到尾部。

`swapBuyAt` 是完整的 bounded N=4 宿主语义；链上 `swapBuy` 用 19-phase
state-carrying fold 实现相同扫描：reset 后，每档依次检查 slot TIF、time TIF、
撮合并推进档位。过期单清零、解锁 base 并继续；第一个超限有效价格停止；整档
成交继续，部分成交停止。无流动性或超限 IOC 成功返回 0，不伪装成 overflow。
`swapBuy` 还按 trader id 执行 Abort / CancelProvide / DecrementTake；自成交量不产生
fill、手续费或 transfer。

quote 和费用先按整次撮合聚合再向上取整。结算扣 `quoteLocked`、增加
`quoteFree`，扣 maker `baseLocked`，把成交和过期解锁量加到 `baseFree`，并增加
`unclaimedFees`；`collectFees` 原子地把它转进 lifetime `collectedFees`。非零成交保留
Token `TransferChecked` CPI。`reduceAsk` 按 trader + `(price, sequence)` 验 owner，
减少 `min(requested, resting)` 并正确解锁 base；缺失订单成功返回 0。

bid-side 对称地按价格降序排列，订单 ID 保存官方的 `~~~sequence` 编码，同价时编码
降序即时间 FIFO。`postBid` 按原价把 quote 从 free 锁入 locked，满书只允许更高价
驱逐最差 bid；`reduceBid` / `cancelBid` 按原价解锁。`swapSell` 扫过期和跨档 bid，
按总成交 adjusted quote 收 taker fee，并覆盖三种 self-trade 行为。宿主递归规范和
链上 structured fold 对样本空间逐项一致。挂单记录 `Evict` / `Place` / `TimeInForce`；
撮合逐档记录 `Fill` / `ExpiredOrder` / self-trade `Reduce`，最后记录
`FillSummary`；reduce 和收取费用分别记录 `Reduce` / `Fee`。事件 batch 的动态
variant-vector 写入通过 target-neutral typed layout 降到两个 target，不需要 emitter
认识 Phoenix。`Place` / `FillSummary` 的 `u128 client_order_id` 用 little-endian
`(lo, hi)` 两个 `UInt64` limb 完整保留；这正好仍落在五 payload 的最大布局内，
所以账户不增大。

真实源模块经 `pf build --target svm Phoenix` 生成 375,120-byte assembly 和
85,248-byte eBPF ELF。测试把 assembly budget 钉在 450 KB，并拒绝重复 label。
链上 buy / sell 分别是 19 / 23 phase，挂单是 17 phase；代码体积按 bounded loop
增长，不按四档静态展开。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| 动态 `RedBlackTree` 删除 fixup | allocator/free-list、完整左右旋和 N=4 insertion fixup 已在独立 Tree refinement 实现；Phoenix 仍用有序投影 |
| `_padding: [u64; 32]` | 不进账户 |
| `Ladder` / `Vec` | 不定长 |
| trader tree / 动态 maker 身份 | 当前双边书仍聚合到一个 bounded TraderState |
| seat lifecycle / 动态 trader registry | 需要更完整账户与身份模型 |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| Borsh wire event / `Log` self-CPI | 当前只存 typed fixed-capacity batch，尚未编码成官方一字节 tag 并发给 event recorder |

这是完整的 bounded N=4 Phoenix IOC 模型，不是完整 Phoenix-v1 动态账户实现。
