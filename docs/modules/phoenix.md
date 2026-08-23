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
| traders tree key / address | `traderKey0..3` 四 limb Pubkey / 1-based `traders`、`bidTraders` |
| traders allocator | `traderCount` / `traderBumpIndex` / `traderFreeHead` / `traderNextFree` |
| 每-seat `TraderState` | 四个 `trader{Quote,Base}{Locked,Free}` 向量 |
| `Side` / `SelfTradeBehavior` | 无 payload 枚举（宿主） |
| `MatchingEngineResponse` | `match*` bounded-fold scratch |
| `MarketEvent` | tag + 五个规范 payload 槽；instruction 内固定容量 5 的 batch |
| TIF 哨兵 0 | `expired`（严格 `<`；等于 deadline 仍有效） |

147 个 8-byte 叶，账户含 discriminator 共 1,184 bytes。`#pf_build Projects.Phoenix`
digest `e263b1245f28c9de`。

`depositFunds` 从 account 1 读取 signer 的完整 32-byte Pubkey。已有 key 幂等复用 seat；
缺失 key 按 Sokoban 的 1-based bump allocator 注册，容量为四个 seat；base/quote 分别
加进该 seat 的 free 余额。全零 Pubkey 也合法，`traderUsed` 单独区分空槽。查找是
structured `forBody 4`，注册和余额更新是通用动态 `Vector.set`，没有 Phoenix-specific
IR 或 emitter 分支。当前撮合仍维护旧的四个聚合兼容槽；下一步是把 post/match/reduce
结算逐项切到这些 per-seat 余额，再删除兼容槽。

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
所以 event layout 未再增大。

真实源模块经 `pf build --target svm Phoenix` 生成 440,512-byte assembly 和
102,664-byte eBPF ELF。assembly 是中间文本，不部署；当前 ELF 约 100 KB。测试把
assembly budget 钉在 450 KB，并拒绝重复 label。
链上 buy / sell 分别是 19 / 23 phase，挂单是 17 phase；代码体积按 bounded loop
增长，不按四档静态展开。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| 动态 `RedBlackTree` 删除 fixup | allocator/free-list、完整左右旋和 N=4 insertion fixup 已在独立 Tree refinement 实现；Phoenix 仍用有序投影 |
| `_padding: [u64; 32]` | 不进账户 |
| `Ladder` / `Vec` | 不定长 |
| trader tree 的动态 RB 拓扑 | 已有 bounded Pubkey registry、allocator 和 per-seat 值；key 查找暂用四槽扫描 |
| 完整 seat lifecycle | deposit/注册已开；withdraw、zero-state eviction 和 free-list reuse transition 尚未接入口 |
| per-seat 撮合结算 / maker Pubkey event | 订单已存内部 seat address，但现有撮合仍写聚合兼容余额，event 尚未 resolve 四 limb key |
| Seat + 双 vault 同一入口 | CPI 账户表会抬高 |
| Borsh wire event / `Log` self-CPI | 当前只存 typed fixed-capacity batch，尚未编码成官方一字节 tag 并发给 event recorder |

这是完整的 bounded N=4 Phoenix IOC 模型，不是完整 Phoenix-v1 动态账户实现。
