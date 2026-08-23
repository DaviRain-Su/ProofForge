# Projects.Phoenix

## Purpose

把 [phoenix-v1](https://github.com/Ellipsis-Labs/phoenix-v1) 的核压进当前 SVM 剖面。这是一个独立用户项目，放在 `Projects/`，不和 `Examples/` 的探针合约混。抽出器按 `@[pf_entry]` 收任意名字空间，不要求前缀是 `Examples.`。

## 本切片有

- 4 档 ask 书：`askPrice` + `sizes : Vector UInt64 4` + `baseFree`
- `postAsk` / `postAsk1`：分别挂档 0 / 档 1（空档才挂）
- `swapBuy` / `swapBuy1`：checked-add `baseFree`，再吃对应档，Token TransferChecked
- `#pf_build Projects.Phoenix`

循环里改状态、四元加法 view 抽出器还不认，所以挂单/吃单按档拆入口，不在一个 `for` 里扫。

## 本切片没有（官方有，剖面关着）

| 官方 | 为什么关 |
|---|---|
| 红黑树 / 512–4096 档 | 不定长 `Array`；有界 `Vector` + for 已开，树还没有 |
| u128 client id / 费用中间量 | 只有 `UInt64` |
| Seat PDA + 多账户图 | 账户叶 0..3；初始化要 System+Token+两个 vault |
| `Log` self-CPI | 变长 event batch |
| PostOnly / 自成交 / TIF / FOK 部分成交 | 要循环走书 |
| Token-2022 | 官方也不做；本仓默认关 |

缺哪块再补 SVM，不要先假装全量兼容。
