# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) 的核压进当前 SVM 剖面。这是一个独立用户项目，放在 `Projects/`，不和 `Examples/` 的探针合约混。抽出器按 `@[pf_entry]` 收任意名字空间，不要求前缀是 `Examples.`。

## 本切片有

- 4 档 ask 书：`askPrice` + `sizes : Vector UInt64 4` + `baseFree`。档 0 是最优
- `postAsk`：挂到第一档空位
- `swapBuy`：只打档 0，且 `want ≤ sizes[0]`。不跳档（官方 FIFO）
- `reduceAsk`：官方 ReduceOrder，只减档 0
- 宿主侧 `sweepAsk` / `cancelAsk` / `checkLimit` / `checkTif` / `takeFee`
- `#pf_build Projects.Phoenix`

官方吃单从最优档开始，允许部分成交，不会跳档。本仓链上 `swapBuy` 还不能吃光档 0（`set 0 0` 抽不出来），部分成交在宿主 `sweepAsk`。

席位 PDA 在 `Examples.Seat`，不跟挂单混 Program。

## 本切片没有（官方有，剖面关着）

| 官方 | 为什么关 |
|---|---|
| 红黑树 / 512–4096 档 | 不定长 `Array` |
| 跨档部分成交 | 要循环走书；`forBody` 抽出还不对 |
| CancelOrder 进链上 | `size - size` 抽不出来 |
| u128 费用 / 限价进入口 | 只有 `UInt64`；先在宿主算 |
| Seat + 双 vault 同一入口 | 两套 recipe 会抬高 `cpiAccountCount` |
| `Log` self-CPI | 变长 event batch |
| Token-2022 | 见 [token-2022.md](../plan/analysis/token-2022.md) |

缺哪块再补 SVM，不要先假装全量兼容。
