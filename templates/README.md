# Templates

ProofForge 用户工程骨架。权威拆分方案见
[`docs/plan/productization.md`](../docs/plan/productization.md)。

| 目录 | Target | 用途 |
|---|---|---|
| [`svm-counter`](svm-counter/) | Solana sBPF | `pf init --target svm` |
| [`evm-counter`](evm-counter/) | EVM Yul | `pf init --target evm` |

当前是 **P2 骨架**：展示推荐 import 与 `pf.toml` 形状。
完整 `pf init` + 可隔离构建依赖 [prod-002](../docs/plan/tasks/prod-002.md) / [prod-003](../docs/plan/tasks/prod-003.md)。

约束：

- 合约只 `import ProofForge.Attr` + 对应 `*.Sdk`
- 不 `import ProofForge` 伞模块
- 不依赖 `Examples` / Emit / Registry
