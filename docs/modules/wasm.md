# ProofForge.Wasm（家族）

## Purpose

WASM 是一个**链家族**，不是一个 target。CosmWasm、Arbitrum Stylus、ink!、NEAR、
ICP、XRPL Bedrock 都编译到 wasm 字节，但各自的 **host function（runtime）** 和
**存储布局**不同。「一份 wasm 走天下」不存在，通用 wasmtime 宿主也不存在
（调研见 [research/06-wasm-feasibility.md](../research/06-wasm-feasibility.md) §四.4）。

产物是 **`.wasm`**。Lean 直接 lowering 到 WAT / wasm，不经过 rustc。Rust 生态的
`cargo` / `xrpl-wasm-std` 是链侧开发者工具，不是 ProofForge 的 Tool Lock。
CLI 的 target 只接受具体链名。

## 结构

```text
ProofForge/Wasm/
  Family.lean     -- 外来叶子 fail-closed 拒绝
  Host.lean       -- 链间差异：host import 表 + 存储布局 + 入口 ABI
  IR.lean         -- 家族共享：程序形状、v0 子集、canonical 拼写（域由链注入）
  Emit.lean       -- 家族共享：Core → WAT
  Xrpl/           -- 每条具体链一个子目录
  Near/           -- 第二条链：NEAR Protocol raw-u64
```

- 家族层共享：svm / evm 叶子的 fail-closed 拒绝，以及 Core 标量 / 控制流到
  WAT 的 lowering。
- 家族层**禁止**共享：Plan、digest 域、host import 表、存储布局。这四样由
  `Wasm/<Chain>/Host` 拥有。
- digest 域由链拥有且互不相同（XRPL 是 `xrpl-bedrock|`）。
- runtime 叶子不跨链：`clockSlot` / `signerKey0` / `systemTransfer` / EVM
  `caller` 等在抽取期即被拒绝。
- 加第二条链时新建 `Wasm/<Chain>/` 并在 CLI 加 `Target.<chain>`，不横向修改
  既有链的方言 / Host / Registry。

## 与 SVM / EVM 的同构

| 层 | SVM | EVM | WASM 链 |
|---|---|---|---|
| 文本 IR | sBPF `.s` | Yul | WAT |
| 锁定组装器 | `sbpf 0.2.2` | `solc 0.8.34` | `wat2wasm`（wsm-002） |
| 链上产物 | `.so` | `.bin` | `.wasm` |
| 链特化 | SVM syscall / 账户布局 | EVM opcode / storage | **host import 表 + 存储布局** |

## 成员

| 链 | 模块 | 状态 |
|---|---|---|
| XRPL Bedrock（XLS-0101） | [`Wasm/Xrpl`](xrpl.md) | Lean → WAT → `.wasm`（wsm-002）；本地四场景（wsm-003）；Runtime 叶子（wsm-005） |
| NEAR Protocol | [`Wasm/Near`](near.md) | Lean → WAT → `.wasm`（raw-u64；[wsm-004](../plan/tasks/wsm-004.md)） |
