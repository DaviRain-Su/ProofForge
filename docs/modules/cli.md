# ProofForge.Cli

## Purpose

`pf`：把 Golden / 抽出后的程序编成目标链制品。

## Surface

```
pf build --target svm [--out DIR] [Name ...]
pf build --target evm [--out DIR] [Name ...]
```

- `svm` / `solana` / `sbpf`：`.so` + `.s` + `.idl.json`
- `evm`：`.bin` + `.yul` + `.abi.json`
- 不写名字 = 该 target 的全部 Golden 夹具
- EVM 叶子的程序不会进 svm 组装

## Tests

`Tests/IdlSpec.lean` 钉 Counter IDL 形状。CLI 本身用 `lake exe pf -- --help`。
