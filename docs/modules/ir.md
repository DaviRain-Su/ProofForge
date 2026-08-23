# Core IR and target ABI

## Purpose

`ProofForge.Core.IR` owns the stable, comparable source-program shape. Target physical
layouts are deliberately outside Core.

## Boundary

Core 记录 source schema、flattened leaves 和方法；`ixName` 是 target 可复用的入口名。
`canonical` / `digestHex` 按 `ixName` 排序后做 FNV-1a 64，不含 Lean 全名与 sketch。
证明主语与发射主语共享这个 source digest。

`ProofForge.Svm.ABI` owns Solana-only account offsets, Loader V3 input layout, account limits,
CPI account counting, instruction discriminators and layout markers. `Svm.IR.fromProgram` then
materializes byte offsets. `Evm.IR.fromProgram` independently materializes storage slots and
selectors. No root `ProofForge.IR` compatibility façade remains.

`Program.schema` / `Method.evaluation` are target-neutral identity and state semantics. The
current compatibility `Ops.Op` still carries target leaves; splitting it into shared control
flow plus target intrinsics is the next boundary, rather than moving the mixed enum unchanged.

## Types

Shared: `ProofForge/Core/IR.lean` (`MethodKind`, `Method`, `Program`).

SVM ABI: `ProofForge/Svm/ABI.lean`. `maxTxAccountLocks = 64` and
`maxAccountsPerInstruction = 255` are not visible from Core or EVM.

## Errors

无。构造是纯数据。

## Tests

T-S0-09：Counter 描述符含三方法。T-L1-13/14：digest 稳定且随 ops 变。T-L2-01/02：Flag / Maybe 槽偏移。
