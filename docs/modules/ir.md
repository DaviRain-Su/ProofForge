# ProofForge.IR

## Purpose

稳定、可比较的 v0 程序形状。语义仍由普通 Lean 函数定义。

## Boundary

记录 `slots`（声明顺序 = 账户槽顺序）和方法。每个槽有名字、字节宽、ABI 后缀。偏移从 header 后累加。`UInt8/16/32/64` 各占 1/2/4/8。`Option UInt64` 展开成 `name_tag` + `name_p0`。`fields` 仍是槽名列表（兼容旧调用）。`ixName` 是链上方法名。`discHex` / `layoutMarkerHex` 由本机 SHA-256 算出，不再挂名表。`inputLayout` 按 `dataLen` 算 Loader V3 偏移。

`Program.schema` / `Method.evaluation` 是 target-neutral 身份与 state semantics。frontend
compatibility `Ops.Op` 到此为止：`Svm.IR.fromProgram` 与 `Evm.IR.fromProgram` 分别复制必要的
method metadata、降到各自独立的 target `Op`，并把 schema 物化成 byte offset 或 storage slot。
两个 emitter 都不再以本模块的 `Program` 作为内部输入。

`canonical` / `digestHex`：按 `ixName` 排序后的规范化文本做 FNV-1a 64。不含 Lean 全名、不含 sketch。证明主语与发射主语必须同一 digest。具体合约夹具在 `ProofForge/Golden.lean`，不进 IR。

## Types

见 `ProofForge/IR.lean`：`MethodKind`、`Method`、`Program`。

账户下标上限是 `maxTxAccountLocks = 64`（Agave 当前强制值；feature 开了才 128）。单条 instruction 编码上限是 `maxAccountsPerInstruction = 255`。

## Errors

无。构造是纯数据。

## Tests

T-S0-09：Counter 描述符含三方法。T-L1-13/14：digest 稳定且随 ops 变。T-L2-01/02：Flag / Maybe 槽偏移。
