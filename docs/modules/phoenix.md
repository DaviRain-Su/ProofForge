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
| `PhoenixMarketEvent` | 官方 ordinal tag + 九个规范 payload 槽；instruction 内固定容量 5 的 batch |
| TIF 哨兵 0 | `expired`（严格 `<`；等于 deadline 仍有效） |

171 个 8-byte 叶，账户含 discriminator 共 1,376 bytes。`#pf_build Projects.Phoenix`
digest 以 `ProofForge.Svm.Registry` 为准（当前 `82953a4d3092eea6`）。

`depositFunds` 从 account 1 读取 signer 的完整 32-byte Pubkey。已有 key 幂等复用 seat；
缺失 key 按 Sokoban 的 1-based bump allocator 注册，容量为四个 seat；base/quote 分别
加进该 seat 的 free 余额。全零 Pubkey 也合法，`traderUsed` 单独区分空槽。查找是
structured `forBody 4`，注册和余额更新是通用动态 `Vector.set`，没有 Phoenix-specific
IR 或 emitter 分支。`withdrawBase` / `withdrawQuote` 分别返回 `min(requested, free)`，
不混淆两种 lot 单位；`evictSeat` 只释放四类余额全零的 seat，并把 address 压回 LIFO
free-list。释放 2 再释放 1 时，后续注册按 1、2 复用且 bump index 不回退。lookup 用
`Except UInt64` producer 汇合到 CFG join local，复合 key guard 由统一 Extract lowering
承载。`postAsk` / `postBid` / `reduceAsk` / `reduceBid` 的链上入口不再接受可伪造的
trader 参数，而是按 account 1 signer 完整 Pubkey 解析内部 seat；reduce/cancel 同时
解锁该 seat 的 base/quote 余额。post 的普通锁仓和满书 eviction 也会原子更新 taker
与被驱逐 maker 的 TraderState；同 owner replacement 先解锁再重新锁仓。matching
现在也逐 event 更新 maker seat，并在 commit 原子更新 registered taker seat。旧的四个
聚合槽继续作为所有 seat 和未注册 take-only fallback 的 compatibility projection；
等双 vault adapter 完成后才能删除 fallback。deposit/withdraw 的 vault Token CPI 仍
属于 adapter 缺口。

`postAsk` 是 signer-authenticated 链上 free-funds 挂单：检查 incoming TIF 和 sequence
上界，把 owner seat 的 `baseFree → baseLocked`，按 `(price, sequence)` 插入有序投影；
书满时只有更低价 ask 能驱逐最差订单，并把旧 maker 的 base 解锁。物理空洞通过
bounded compare/swap 收到尾部。未注册 trader 只保留在宿主 reference helper 的
aggregate fallback，真实 instruction 先经过完整 Pubkey lookup，不能进入该分支。

`swapBuyAt` 是完整的 bounded N=4 宿主语义；链上 `swapBuy` 用 19-phase
state-carrying fold 实现相同扫描：reset 后，每档依次检查 slot TIF、time TIF、
撮合并推进档位。过期单清零、解锁 base 并继续；第一个超限有效价格停止；整档
成交继续，部分成交停止。无流动性或超限 IOC 成功返回 0，不伪装成 overflow。
`swapBuy` / `swapSell` 不再接受可伪造的 taker seat：都从 account 1 signer 的完整
Pubkey 查找 seat，未注册 signer 映射到 take-only sentinel，再按该身份执行 Abort /
CancelProvide / DecrementTake。自成交量不产生 fill、手续费或 transfer，ABI 也从
六个参数缩到五个。

quote 和费用先按整次撮合聚合再向上取整。每个 ask fill 执行 maker
`baseLocked → quoteFree`；过期和 self-cancel 执行 maker `baseLocked → baseFree`。
registered free-funds buy 从 taker `quoteFree` 扣成交额和费用，再把成交量加进
`baseFree`。这些 seat transition 和 aggregate compatibility projection 同步提交，
并增加 `unclaimedFees`；`collectFees` 原子地把它转进 lifetime `collectedFees`。
registered 路径不做 vault CPI；未注册 take-only 暂保留旧 aggregate 结算和单边
`TransferChecked` 占位，真正的双 vault 输入/输出 adapter 尚未完成。`reduceAsk` 按
signer seat + `(price, sequence)` 验 owner，减少 `min(requested, resting)`；缺失订单
成功返回 0。

bid-side 对称地按价格降序排列，订单 ID 保存官方的 `~~~sequence` 编码，同价时编码
降序即时间 FIFO。`postBid` 同样按 signer seat 授权，按原价把 quote 从 free 锁入
locked，满书只允许更高价驱逐最差 bid，并在不同 maker/taker seat 间原子移动 collateral；
`reduceBid` / `cancelBid` 按原价解锁 owner seat 的 quote collateral。
`swapSell` 扫过期和跨档 bid，
按总成交 adjusted quote 收 taker fee；maker fill 执行 `quoteLocked → baseFree`，
registered taker 执行 `baseFree → quoteFree`，过期和 self-cancel 解锁 maker quote。
宿主递归规范和链上 structured fold 对逐 seat 余额及 aggregate 投影逐项一致。挂单
记录 `Evict` / `Place` / `TimeInForce`；
撮合逐档记录 `Fill` / `ExpiredOrder` / self-trade `Reduce`，最后记录
`FillSummary`；reduce 和收取费用分别记录 `Reduce` / `Fee`。事件 batch 的动态
variant-vector 写入通过 target-neutral typed layout 降到两个 target，不需要 emitter
认识 Phoenix。ordinal 对齐官方 wire enum：0 Uninitialized、1 Header、2 Fill、3 Place、
4 Reduce、5 Evict、6 FillSummary、7 Fee、8 TimeInForce、9 ExpiredOrder。每个实际事件
携带 instruction 内 index；maker-bearing Fill/Evict/ExpiredOrder 在构造前把内部 seat
解析成完整四 limb Pubkey。事件 batch 满 5 条时 instruction fail-closed（`.full` /
`0x1003`），不再静默丢事件仍返回成功。`Error` 现为 `overflow` / `unauthorized` /
`full` / `selfTrade`，链上分别是 `0x1001` / `0x1002` / `0x1003` / `0x1004`。`Place` / `FillSummary` 的 `u128 client_order_id` 继续用
little-endian `(lo, hi)` 两个 `UInt64` limb 完整保留。最宽事件现在是九 payload，测试
明确钉住动态 `events` 的 byte offset 72，防止抽取器静默漏掉尾叶。

真实源模块经 `pf build --target svm Phoenix` 生成 5,613,720-byte assembly、
841,984-byte eBPF ELF 和 12,974-byte IDL。assembly 是未做 CSE/共享基本块的中间文本，
不是部署文件；当前 ELF 约 822.3 KiB。完整 maker Pubkey 与 event/lastEvent 双写会重复
展开 conditional values，因此文本体积明显增加。测试把 assembly 回归预算钉在
5.75 MB，并拒绝重复 label，同时断言 maker/taker ledger writes 和最宽 event leaf
都存在。链上 buy / sell 都是 19 phase，挂单是 17 phase；要显著缩小文件应在通用
IR/CFG 做 local CSE 或共享 block，而不是在 Phoenix 或 target emitter 加事件特判。

## 官方有、本仓没有

| 官方 | 为什么关 |
|---|---|
| 动态 `RedBlackTree` 删除 fixup | allocator/free-list、完整左右旋和 N=4 insertion fixup 已在独立 Tree refinement 实现；Phoenix 仍用有序投影 |
| `_padding: [u64; 32]` | 不进账户 |
| `Ladder` / `Vec` | 不定长 |
| trader tree 的动态 RB 拓扑 | 已有 bounded Pubkey registry、allocator 和 per-seat 值；key 查找暂用四槽扫描 |
| vault-backed seat lifecycle | bounded deposit/withdraw/zero-state eviction/LIFO reuse 已完成；双 vault Token CPI 尚未接这些入口 |
| Seat + 双 vault 同一入口 | state transition 已有；CPI 账户表会抬高 |
| `AuditLogHeader` / Borsh wire event / `Log` self-CPI | ordinal 1 只留 Header 占位；尚未编码真实 header 和窄字段，也未发给 event recorder |

这是完整的 bounded N=4 Phoenix IOC 模型，不是完整 Phoenix-v1 动态账户实现。
