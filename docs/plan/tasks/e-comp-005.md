---
id: e-comp-005
scope: evm
status: done
depends-on: [e-comp-004]
---

# e-comp-005 给 hashed-map 加源侧静态 handle

## objective

借鉴 SVM `AccountStorage.Source`：合同代码命名一个编译期 hashed-map handle，只把动态
key/value 传给 source 操作。`@[pf_inline]` 在抽出时消去 handle，落到已有
`Evm.HashedMap` component 计划。不新增 Ops / IR / 主 Emit case，digest 不变。

- `Evm.HashedMap.Source` 提供 `MapU64` / `MapAddr` / `MapPair` / `MapAddr256` /
  `MapPair256` 以及 get/set
- Extract 对 `@[pf_inline]` 包装展开 UInt256 / Addr20 读和 EVM effect walk
- Token / Vault / Ownable 改用 named handles，不再把 `balBase` / `shareBase` 当裸
  `UInt64` 传给 runtime

## 不做

ClosedCall Source；pause / cap / Ownable mint；generic CALL。
