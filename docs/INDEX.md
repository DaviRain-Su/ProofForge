# ProofForge 文档索引

独立仓：用**普通 Lean 4** 写合约，复用 Lean kernel / elaborator / tactic，只自建目标剖面和 IR 胶水。当前目标是 Solana sBPF 和 EVM Yul。

| 文档 | 作用 |
|---|---|
| [README.md](../README.md) | 仓库入口与当前范围 |
| [00-business-validation.md](00-business-validation.md) | 为什么做、为什么现在做 |
| [01-prd.md](01-prd.md) | 做 / 不做 |
| [02-architecture.md](02-architecture.md) | 模块边界与信任边界 |
| [03-technical-spec.md](03-technical-spec.md) | v0 切片的具体契约 |
| [04-task-breakdown.md](04-task-breakdown.md) | 阶段与任务 |
| [05-test-spec.md](05-test-spec.md) | 怎样算对 |
| [plan/README.md](plan/README.md) | 交付队列 |
| [plan/analysis/authority.md](plan/analysis/authority.md) | 补全对谁对齐（官方 runtime，不是 SDK crate） |
| [plan/analysis/gap-vs-proofforge.md](plan/analysis/gap-vs-proofforge.md) | 相对 PF 的缺口与阶段 |
| [plan/analysis/sdk-surface.md](plan/analysis/sdk-surface.md) | 剩余 SDK 表面（syscall / 封闭 CPI） |
| [plan/analysis/remaining-surface.md](plan/analysis/remaining-surface.md) | 第 1/2 层收口清单 |
| [modules/README.md](modules/README.md) | 模块合同 |
| [modules/evm.md](modules/evm.md) | EVM 平行发射器 |
| [research/03-feasibility.md](research/03-feasibility.md) | Solana 可行性调研结论 |
| [research/04-evm-feasibility.md](research/04-evm-feasibility.md) | EVM target：按当前 Lean 4 表面能否做 |
| [research/05-evm-coverage-slices.md](research/05-evm-coverage-slices.md) | EVM 覆盖缺口与三块大切片 |

当前阶段：**L4 + EVM**。仓库名 ProofForge；入口 `@[pf_entry]`；CLI `pf`。E-TOK 已并入：本合约余额 + 真额度扣减。SVM 名不翻译。
