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
| [modules/README.md](modules/README.md) | 模块合同 |
| [research/03-feasibility.md](research/03-feasibility.md) | 可行性调研结论 |

当前阶段：**S1/S2 已绿**。下一步 S3：接 ProofForge `emitSbpfAsmV1`。
