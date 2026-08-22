# SolanaLean.Emit

## Purpose

把 v0 Counter IR 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

Load 由 `Val` 决定：`.field _ "value"` → `ACC0_DATA+8`；`.arg _` → `INSTRUCTION_DATA+8`。对调 `checkedAddU64` 左右操作数会改变第一条 load。空 ops 失败。

## API

`emitCounterAsm : IR.Program → Except String String`

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean`：含 `entrypoint`、checked-add overflow、layout marker、三 discriminator、`sol_set_return_data`；空 IR 拒绝。
