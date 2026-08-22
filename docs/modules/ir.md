# SolanaLean.IR

## Purpose

稳定、可比较的 v0 程序形状。语义仍由普通 Lean 函数定义。

## Boundary

记录 `fields`（声明顺序 = 账户槽顺序）和方法。偏移 = `8 + index * 8`。`layoutSig` / `layoutMarkerHex` 按 PF `proof-forge-solana-layout-v1:` 公式；仅登记已知字段表。单字段 `value` 的布局名是 `count`（StateCell ABI）。`inputLayout` 按 `dataLen` 算 Loader V3 的 `INSTRUCTION_DATA` 偏移（16 字节账户 = `0x2880`，24 字节 = `0x2888`）。

## Types

见 `SolanaLean/IR.lean`：`MethodKind`、`Method`、`Program`。

## Errors

无。构造是纯数据。

## Tests

T-S0-09：Counter 描述符含三方法。
