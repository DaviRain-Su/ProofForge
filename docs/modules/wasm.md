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
  Family.lean     -- 家族级约定：外来叶子 fail-closed 拒绝 + 错误消息语法
  Xrpl/           -- 每条具体链一个子目录（Ops / IR / Emit / Registry / Assemble / Commands）
```

- 家族层（`Wasm.Family`）**只**共享跨链必然成立的最小约定：对 svm / evm 叶子的
  fail-closed 投影拒绝（`rejectValKind` / `rejectOpExt`，以链名为前缀的消息）。
- 家族层**禁止**共享：Plan、target IR、emitter、digest 域、宿主合同。这些全部
  由具体链子目录拥有；加第二条 WASM 链时新建 `Wasm/<Chain>/` 并在 CLI 加
  `Target.<chain>`，不横向修改既有链（同一纪律的先例：旧仓 proof_forge 的
  `family-wasm-host.md` 禁 `GenericWasmHostPlan`）。
- digest 域由链拥有且互不相同（XRPL 是 `xrpl-bedrock|`），artifact 永不跨链混淆。
- runtime 叶子不跨链：`clockSlot` / `signerKey0` / `systemTransfer` / EVM
  `caller` 等在抽取期即被拒绝。

## 成员

| 链 | 模块 | 状态 |
|---|---|---|
| XRPL Bedrock（XLS-0101） | [`Wasm/Xrpl`](xrpl.md) | v0 source-only（Counter 竖切） |