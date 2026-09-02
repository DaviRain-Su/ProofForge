# EVM Counter 模板（骨架）

> 状态：产品化 P2 骨架。`pf init --target evm` 将复制本目录。
> 在 prod-002 完成 Lake `ProofForgeEvmSdk` 拆分之前，请在 monorepo 内用
> `Examples` + `lake exe pf` 开发；本模板展示 **目标工程形状**。

## 目标形状

- 只依赖 EVM SDK（+ Attr），不 import `ProofForge` 伞模块 / Emit / Registry。
- `pf.toml` 声明模块路径，CLI 不再假设 `Examples.*`。
- `lake build` 类型检查合约；`pf build --target evm` 产出 `.bin` / `.yul` / `.abi.json`。

## 生成后用法（P2 落地后）

```bash
pf init my-contract --target evm
cd my-contract
pf build --target evm
```

参考仓内好例子：`Examples/Evm/TipJar.lean`（`import ProofForge.Evm.Sdk`）。
