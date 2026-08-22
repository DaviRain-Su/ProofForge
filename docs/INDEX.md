# solana-lean 文档索引

独立仓：用**普通 Lean 4** 写 Solana 合约，复用 Lean kernel / elaborator / tactic，只自建目标剖面和 IR 胶水；sBPF 发射与汇编复用 ProofForge 已有 lowering。

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
| [modules/README.md](modules/README.md) | 模块合同 |
| [research/03-feasibility.md](research/03-feasibility.md) | 可行性调研结论 |

当前阶段：**L4 SDK 表面**。L4-028：tokenSyncNative。
