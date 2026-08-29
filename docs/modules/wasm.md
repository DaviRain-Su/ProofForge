# ProofForge.Wasm（家族）

## Purpose

WASM 是一个**链家族**，不是一个 target。CosmWasm、Arbitrum Stylus、ink!、NEAR、
XRPL Bedrock 各自拥有不同的 host function、存储模型、入口 ABI 和 gas 规则；
「一份 wasm 走天下」不存在（调研见
[research/06-wasm-feasibility.md](../research/06-wasm-feasibility.md) §四.4）。
因此本仓的 WASM 支持按**每链一个 target**组织，CLI 的 target 也只接受具体链名。

## 结构

```text
ProofForge/Wasm/
  Family.lean     -- 外来叶子 fail-closed 拒绝 + 错误消息语法
  Host.lean       -- 链间差异的注入面（存储 / host import / 入口 ABI）
  IR.lean         -- 家族共享：程序形状、v0 子集、canonical 拼写（域由链注入）
  Emit.lean       -- 家族共享：Core → Rust 发射（host contract 注入链特化文本）
  Xrpl/           -- 每条具体链一个子目录
```

- 家族层共享跨链必然成立的约定：对 svm / evm 叶子的 fail-closed 投影拒绝
  （`rejectValKind` / `rejectOpExt`，以链名为前缀的消息），以及经 Rust 编译到
  wasm 的链所共用的 Core→Rust 程序形状、v0 子集检查、canonical 拼写和发射器。
- 家族层**禁止**共享：Plan、digest 域字符串、宿主合同实例。这三样由
  `Wasm/<Chain>/` 拥有（`Host.contract` 注入发射器）。旧仓 `family-wasm-host.md`
  禁的是 `GenericWasmHostPlan`——一份假装通用的宿主合同——不是禁 Core→Rust
  的共享 lowering。
- digest 域由链拥有且互不相同（XRPL 是 `xrpl-bedrock|`），artifact 永不跨链混淆。
- runtime 叶子不跨链：`clockSlot` / `signerKey0` / `systemTransfer` / EVM
  `caller` 等在抽取期即被拒绝。
- 加第二条 WASM 链时新建 `Wasm/<Chain>/` 并在 CLI 加 `Target.<chain>`，不横向
  修改既有链的方言 / Host / Registry。

## 成员

| 链 | 模块 | 状态 |
|---|---|---|
| XRPL Bedrock（XLS-0101） | [`Wasm/Xrpl`](xrpl.md) | v0 source-only（Counter 竖切） |
