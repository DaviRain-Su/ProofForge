# SolanaLean.Emit

## Purpose

把 v0 Counter IR 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

Load 由 `Val` 决定：`.field _ name` → `ACC0_DATA + fieldOffset`；`.arg _` → `INSTRUCTION_DATA+8`。layout marker 与 `INSTRUCTION_DATA*` 按 `Program` 取。dispatch 按每个 method 的 `ixName` 取已登记 discriminator。`okState` 写回目标取同序列 checked 算术的 lhs（Pair.creditLeft 抽出的 `okState (field right)` 仍写 left）。空 ops 失败。

## API

`emitCounterAsm : IR.Program → Except String String`

汇编头含 `digest=`（`IR.digestHex`）。

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean`：含 `entrypoint`、checked-add overflow、layout marker、三 discriminator、`sol_set_return_data`；空 IR 拒绝。
