# SolanaLean.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

先 `Profile.checkAll`。不解释运算语义。改函数体（增减引用的常量）必须改变 sketch。

## API

- `extractCounter env init increment get : Except String IR.Program`
- `#solana_extract init increment get`

## Tests

`Tests/ExtractSpec.lean`：Counter 抽出成功；夹带 `usesNat` fail closed。
