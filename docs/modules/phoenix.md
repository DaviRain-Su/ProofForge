# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) 的核压进当前 SVM 剖面。这是一个独立用户项目，放在 `Projects/`，不和 `Examples/` 的探针合约混。抽出器按 `@[pf_entry]` 收任意名字空间，不要求前缀是 `Examples.`。

## 本切片有

- 4 档 ask 书：`askPrice` + `sizes : Vector UInt64 4` + `baseFree`
- `postAsk`：一个入口扫到第一档空位
- `swapBuy`：一个入口从档 0 扫到 3，第一档装得下就成交 + Token TransferChecked
- 宿主侧 `checkLimit` / `checkTif` / `takeFee`（UInt64 bps，不是官方 u128）
- `#pf_build Projects.Phoenix`

`askQty` 是四档 wrapping 加。挂单/吃单用展开的 4 路 `ite`。
`Op.forBody` 已开，但抽出器还分不清循环 binder 和外层参数，所以 Phoenix 还没收成 `for`。

席位 PDA 在 `Examples.Seat`，不跟挂单混 Program。

## 本切片没有（官方有，剖面关着）

| 官方 | 为什么关 |
|---|---|
| 红黑树 / 512–4096 档 | 不定长 `Array`；有界 `Vector` + for 已开，树还没有 |
| u128 client id / 费用中间量 | 只有 `UInt64`；bps 费用先在宿主算 |
| Seat + 双 vault 同一入口 | 两套 recipe 会抬高 `cpiAccountCount` |
| `Log` self-CPI | 变长 event batch |
| PostOnly / 自成交 / 跨档部分成交 | 要循环走书；`forBody` 抽出还不对 |
| Token-2022 | 见 [token-2022.md](../plan/analysis/token-2022.md)；没有 Token v3 |

缺哪块再补 SVM，不要先假装全量兼容。
