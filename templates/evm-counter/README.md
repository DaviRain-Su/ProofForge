# EVM Counter 模板

> `pf init --target evm` 复制本目录。monorepo/`pf init` 默认 path-`require` 本仓；
> 发布后改为 `require «proofforge» from git … @ "v0.0.1"`（见 [release-001](../../docs/plan/tasks/release-001.md)）。

## 目标形状

- 只依赖 EVM SDK（+ Attr），不 import `ProofForge` 伞模块 / Emit / Registry。
- `pf.toml` 声明模块路径，CLI 不再假设 `Examples.*`。
- `lake build` 类型检查合约；`pf build --target evm` 产出 `.bin` / `.yul` / `.abi.json`。

## 用法

```bash
pf init my-contract --target evm
cd my-contract
lake build && lake env pf build --target evm
# 或：lake exe pf -- build --target evm
```

参考仓内好例子：`Examples/Evm/TipJar.lean`（`import ProofForge.Evm.Sdk`）。
