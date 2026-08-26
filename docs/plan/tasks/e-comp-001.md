---
id: e-comp-001
scope: evm
status: done
depends-on: [e-meta-001]
---

# e-comp-001 EVM Component 桥：主链路只留一个口

## objective

借鉴 SVM `Svm.Component.Query/Call`：generic EVM Ops / IR / Extract 遍历 / 主 Emit 只认一个 `.component` case。新的封闭能力扩 component-owned vocabulary，不再给 `ValKind` / `OpExt` / `IR.Op` / Emit 各加一个平行构造子。

- 现有 hashed-map / LOG3 / permit / swap 叶本轮不迁，digest 不变
- 第一个 backend 先空着：`Query` / `Call` 是空归纳，只证明主链路能投影、遍历、发射
- 源程序不使用 component 时，Yul / ABI / Anvil 与现在一致

## 不做

搬 SVM AccountStorage / EntryAdapter / Heap；改 Token 源；把现有 map/CALL 叶收进 component。
