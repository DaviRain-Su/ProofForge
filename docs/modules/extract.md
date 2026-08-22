# SolanaLean.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`。可变方法无守卫则 fail closed。

## API

- `extractCounter env init increment get : Except String IR.Program`
- `#solana_extract init increment get`

## Tests

`Tests/ExtractSpec.lean`：Counter 抽出成功；夹带 `usesNat` fail closed。
