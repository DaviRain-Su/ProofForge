# Core IR and target ABI

## Purpose

`ProofForge.Core.IR` owns the stable, comparable source-program shape. Target physical
layouts are deliberately outside Core.

## Boundary

Core 记录 source schema、flattened leaves 和方法；`ixName` 是 target 可复用的入口名。
`canonical` / `digestHex` 按 `ixName` 排序后做 FNV-1a 64，不含 Lean 全名与 sketch。
证明主语与发射主语共享这个 source digest。

`ProofForge.Svm.ABI` owns Solana-only account offsets, Loader V3 input layout, account limits,
CPI account counting, instruction discriminators and layout markers. `Svm.IR.fromExtracted` then
materializes byte offsets. `Evm.IR.fromExtracted` independently materializes storage slots and
selectors. No root `ProofForge.IR` compatibility façade remains.

`Program.schema` / `Method.evaluation` are target-neutral identity and state semantics.
`Core.Target.Registration` recursively projects all common Core values/ops and delegates only
extension leaves/effects to a target-owned callback. It also carries target value arity,
op well-formedness and CFG dialect, so projection validates before physical lowering. SVM/EVM
registrations live in their own IR modules; `Extract.IR` no longer contains backend conversion
functions. A backend accepting the existing common language therefore does not add a case to
`Extract.IR`. A genuinely new source/runtime intrinsic still extends the frontend dialect.

## Types

Shared: `ProofForge/Core/IR.lean` (`MethodKind`, `Method`, `Program`) and
`ProofForge/Core/Target.lean` (`Registration`, generic value/op/program projection).

SVM ABI: `ProofForge/Svm/ABI.lean`. `maxTxAccountLocks = 64` and
`maxAccountsPerInstruction = 255` are not visible from Core or EVM.

## Errors

投影对 foreign extension、extension arity、target op well-formedness 或 CFG validation
失败时 fail closed。

## Tests

T-S0-09：Counter 描述符含三方法。T-L1-13/14：digest 稳定且随 ops 变。T-L2-01/02：Flag / Maybe 槽偏移。`TargetOpsSpec` 的 Core-only 合成第三 target 覆盖无 `Extract.IR` 修改的注册路径及 foreign-extension 拒绝。
