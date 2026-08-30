# ProofForge 文档索引

独立仓：用**普通 Lean 4** 写合约，复用 Lean kernel / elaborator / tactic，只自建目标剖面和 IR 胶水。当前目标是 Solana sBPF 和 EVM Yul。

| 文档 | 作用 |
|---|---|
| [README.md](../README.md) | 仓库入口与当前范围 |
| [00-business-validation.md](00-business-validation.md) | 为什么做、为什么现在做 |
| [01-prd.md](01-prd.md) | 做 / 不做 |
| [02-architecture.md](02-architecture.md) | 当前模块边界、信任边界与早期迁移背景 |
| [03-technical-spec.md](03-technical-spec.md) | 历史 v0 Counter 切片（非当前权威） |
| [04-task-breakdown.md](04-task-breakdown.md) | 阶段与任务 |
| [05-test-spec.md](05-test-spec.md) | 怎样算对 |
| [plan/README.md](plan/README.md) | 交付队列 |
| [plan/runtime-sdk-roadmap.md](plan/runtime-sdk-roadmap.md) | SVM / EVM Runtime 与 SDK 的权威边界、排期和验收门 |
| [plan/capability-matrix.md](plan/capability-matrix.md) | source API → owner → component → target effect → 物理状态能力矩阵 |
| [plan/mainstream-parity.md](plan/mainstream-parity.md) | 对照 Solana Rust SDK 与 Solidity/OpenZeppelin 的双目标能力基线和 F0–F3 优先级 |
| [plan/analysis/authority.md](plan/analysis/authority.md) | 补全对谁对齐（官方 runtime，不是 SDK crate） |
| [plan/analysis/gap-vs-proofforge.md](plan/analysis/gap-vs-proofforge.md) | 相对 PF 的缺口与阶段 |
| [plan/analysis/sdk-surface.md](plan/analysis/sdk-surface.md) | 剩余 SDK 表面（syscall / 封闭 CPI） |
| [plan/analysis/remaining-surface.md](plan/analysis/remaining-surface.md) | 第 1/2 层收口清单 |
| [plan/analysis/token-2022.md](plan/analysis/token-2022.md) | Token-2022；没有 Token v3 |
| [modules/README.md](modules/README.md) | 模块合同 |
| [modules/evm.md](modules/evm.md) | EVM 平行发射器 |
| [modules/solanalib.md](modules/solanalib.md) | bounded typed sBPF semantics bridge |
| [research/03-feasibility.md](research/03-feasibility.md) | Solana 可行性调研结论 |
| [research/04-evm-feasibility.md](research/04-evm-feasibility.md) | EVM target：按当前 Lean 4 表面能否做 |
| [research/05-evm-coverage-slices.md](research/05-evm-coverage-slices.md) | EVM 覆盖缺口与三块大切片 |
| [research/06-wasm-feasibility.md](research/06-wasm-feasibility.md) | WASM 第三 target：Lean 自家编译器 vs 新 profile 的路线判定 |
| [modules/wasm.md](modules/wasm.md) | WASM 链家族：Lean → `.wasm`；链拥有 host import 表与存储布局 |
| [modules/xrpl.md](modules/xrpl.md) | WASM 家族成员：XRPL Bedrock Lean → WAT → `.wasm` |
| [plan/analysis/xrpl-runtime.md](plan/analysis/xrpl-runtime.md) | XRPL Runtime 排期：向 EVM/SVM 学分层，不学物理模型 |
| [plan/analysis/xrpl-model.md](plan/analysis/xrpl-model.md) | XRPL WASM 账本模型 vs EVM / SVM / NEAR；为什么生态不像 NEAR |
| [plan/analysis/xrpl-xls.md](plan/analysis/xrpl-xls.md) | XLS-30 等协议对象 vs WASM：不要用合约重写主网 amendment |
| [plan/analysis/xrpl-local.md](plan/analysis/xrpl-local.md) | 本地 2.6.1 先做；公开 -196/-22 先放 |
| [modules/near.md](modules/near.md) | WASM 家族成员：NEAR Protocol Lean → WAT → `.wasm`（raw-u64） |

当前阶段：**L4 + EVM + WASM 家族 XRPL / NEAR（`.wasm` v0）**。仓库名 ProofForge；入口 `@[pf_entry]`；CLI `pf`。E-ADDR / E-U256 已并入：`Addr20` 是 `address`，`UInt256` 是显式 `uint256`。SVM 名不翻译。XRPL 不翻译成 `clockSlot` / `CALLER`。
