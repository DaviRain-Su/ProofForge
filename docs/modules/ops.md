# SolanaLean.Ops

## Purpose

从 elaborated `Expr` 抽出的 v0 操作。发射 overflow 路径的依据是 `checkedAddU64`，不是方法名。

## Types

`Val`：`arg` / `field` / `add` / `subFromMax`  
`Op`：`checkedAddU64` / `okState` / `errorOverflow` / `returnU64` / `returnState`

## Tests

`increment` 必须抽出 `checkedAddU64`；`wrappingAdd` fail closed。
