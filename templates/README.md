# Templates

ProofForge 用户工程骨架。权威拆分方案见
[`docs/plan/productization.md`](../docs/plan/productization.md)。

| 目录 | Target | 用途 |
|---|---|---|
| [`svm-counter`](svm-counter/) | Solana sBPF | `pf init --target svm` |
| [`evm-counter`](evm-counter/) | EVM Yul | `pf init --target evm` |

`pf init <name> --target svm|evm` 会复制对应目录，并把
`require … from ".." / ".."` 改写成相对 monorepo 根的路径（通常为 `..`）。

约束：

- 合约只 `import ProofForge.Attr` + 对应 `*.Sdk`
- 不 `import ProofForge` 伞模块
- 不依赖 `Examples` / Emit / Registry

上手：

```text
pf init demo --target svm
cd demo && lake build
lake exe pf -- build --target svm   # 读取 pf.toml 的 [[program]]
```
