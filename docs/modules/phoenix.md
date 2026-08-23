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
| TIF 哨兵 0 | `expired`（严格 `<`；等于 deadline 仍有效） |

67 个 u64 槽，账户含 discriminator 共 544 bytes。`#pf_build Projects.Phoenix`
digest `13a349638aa8c993`。

`postAsk` 是链上 free-funds 挂单：检查 incoming TIF 和 sequence 上界，锁定
`baseFree → baseLocked`，按 `(price, sequence)` 插入有序投影；书满时只有更低价
ask 能驱逐最差订单。物理空洞通过 bounded compare/swap 收到尾部。

`swapBuyAt` 是完整的 bounded N=4 宿主语义；链上 `swapBuy` 用 17-phase
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
链上 17-phase fold 对样本空间逐项一致。

真实源模块经 `pf build --target svm Phoenix` 生成 356,713-byte assembly 和
90,504-byte eBPF ELF。增加完整 bid-side 后 ELF 只增加 34,536 bytes；测试把
assembly budget 钉在 450 KB，并拒绝重复 label。当前体积仍很小，两个方向都按
独立 bounded loop 增长，不按四档静态展开。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| 动态 `RedBlackTree` 删除 fixup | allocator/free-list、完整左右旋和 N=4 insertion fixup 已在独立 Tree refinement 实现；Phoenix 仍用有序投影 |
| `_padding: [u64; 32]` | 不进账户 |
| `OrderPacket.client_order_id: u128` | 只有 `UInt64` |
| `MarketEvent` 带 payload | 多构造子 inductive |
| `Ladder` / `Vec` | 不定长 |
| trader tree / 动态 maker 身份 | 当前双边书仍聚合到一个 bounded TraderState |
| seat lifecycle / event batch | 需要更完整账户与事件模型 |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| `Log` self-CPI | 变长 event batch |

这是完整的 bounded N=4 Phoenix IOC 模型，不是完整 Phoenix-v1 动态账户实现。
