# ProofForge.Svm.Idl

## Purpose

从抽出的 `IR.Program` 写 Solana IDL spec `0.1.0` JSON。不是链上字节的一部分。

## Boundary

- disc = `sha256("proof-forge-solana-v1:" ++ name ++ "(" ++ sig ++ ")")` 前 8 字节，小端
- 账户类型 disc = layout marker 的 8 字节大端
- `address` 占位 `1111…11`，部署后再填
- 账户表：acc0 = `state`；CPI 程序再列 `acc1…`。旗是保守默认（mutate 时 acc0 signer+writable）

## Output

`Name.idl.json`，与 `.so` 一起由 `pf build --target svm` 写出。
