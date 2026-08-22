# SolanaLean.Emit

## Purpose

把 v0 Counter IR 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

Handler 体按 `Method.ops` 选择片段：`returnState` → init 写回；`checkedAddU64`+`errorOverflow` → overflow `0x1001`；`returnU64` → `sol_set_return_data`。空 ops 失败。Loader 预检仍共享。不调用 PF `IR.mk`。

## API

`emitCounterAsm : IR.Program → Except String String`

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean`：含 `entrypoint`、checked-add overflow、layout marker、三 discriminator、`sol_set_return_data`；空 IR 拒绝。
