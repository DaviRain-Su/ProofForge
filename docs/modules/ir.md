# SolanaLean.IR

## Purpose

稳定、可比较的 v0 程序形状。语义仍由普通 Lean 函数定义。

## Boundary

只记录方法名与 kind。不记录 sBPF、账户字节。

## Types

见 `SolanaLean/IR.lean`：`MethodKind`、`Method`、`Program`。

## Errors

无。构造是纯数据。

## Tests

T-S0-09：Counter 描述符含三方法。
