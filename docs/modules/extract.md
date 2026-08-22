# SolanaLean.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

先 `Profile.checkAll`。认出 `ite` + `LE.le` + `u64Max -` 为 `checkedAddU64`。无保护加法 fail closed。

## API

- `extractCounter env init increment get : Except String IR.Program`
- `#solana_extract init increment get`

## Tests

`Tests/ExtractSpec.lean`：Counter 抽出成功；夹带 `usesNat` fail closed。
