# SolanaLean.IR

## Purpose

稳定、可比较的 v0 程序形状。语义仍由普通 Lean 函数定义。

## Boundary

记录 `fields`（声明顺序 = 账户槽顺序）和方法。`ixName` 是链上方法名（Lean `init` → `initialize`）。`discHex` 按 PF `proof-forge-solana-v1:` 公式，仅登记已知名。偏移 = `8 + index * 8`。`layoutSig` / `layoutMarkerHex` 按 PF layout 公式。`inputLayout` 按 `dataLen` 算 Loader V3 偏移。

`canonical` / `digestHex`：按 `ixName` 排序后的规范化文本做 FNV-1a 64。不含 Lean 全名、不含 sketch。证明主语与发射主语必须同一 digest。

## Types

见 `SolanaLean/IR.lean`：`MethodKind`、`Method`、`Program`。

## Errors

无。构造是纯数据。

## Tests

T-S0-09：Counter 描述符含三方法。T-L1-13/14：digest 稳定且随 ops 变。
