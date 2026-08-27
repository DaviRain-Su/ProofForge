# ProofForge.Cli

## Purpose

`pf`：把源模块抽出后编成目标链制品。`Svm.Registry` / `Evm.Registry` 只登记
源码模块名并钉 target IR digest，不能替代源模块 IR，也不依赖旧 mixed Golden。

## Surface

```
pf build --target svm [--out DIR] [Name ...]
pf build --target evm [--out DIR] [Name ...]
```

- `svm` / `solana` / `sbpf`：`.so` + `.s` + `.idl.json`
- `evm`：`.bin` + `.yul` + `.abi.json`
- SVM 每次运行时加载 `Examples.Name` 并重新抽 IR；Phoenix 不再需要目录特判；
  digest 必须与 Golden 一致
- 不写名字 = SVM 的全部登记源模块 / EVM 的全部 Golden 夹具
- EVM 叶子的程序不会进 svm 组装

## Tests

`Tests/IdlSpec.lean` 钉 Counter IDL 形状。CLI 本身用 `lake exe pf -- --help`；
Phoenix 用真实源模块构建并检查 ELF，不再组装陈旧 smoke fixture。
