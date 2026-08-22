# SolanaLean.Emit

## Purpose

把 v0 Counter IR 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

不调用 PF 的私有 `IR.mk`。不调用 `sbpf`（S4）。布局 / discriminator / overflow `0x1001` 与 PF StateCell 黄金文件一致，便于后续 Mollusk 复用同一夹具。

## API

`emitCounterAsm : IR.Program → Except String String`

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean`：含 `entrypoint`、checked-add overflow、layout marker、三 discriminator、`sol_set_return_data`；空 IR 拒绝。
