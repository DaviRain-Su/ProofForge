---
id: svm-rt-004
track: B-runtime
status: done
plan: ../svm-work-plan.md
priority: F2
---

# svm-rt-004 Instructions / sliced sysvar（有界）

## 目标

按需提供有界 Instructions sysvar 或固定偏移切片；不是通用任意切片 API。

## 交付

1. 编译期 bound 的只读视图
2. OOB / 短账户 fail closed
3. Mollusk 正反例

## 非目标

`get_sysvar` 任意 blob；feature-gated 高级 sysvar 全家桶。

## 验收证据

- SDK：`ProofForge/Svm/Sdk/SysvarSlice.lean` — compile-time `Slice` / `Instructions` + `numInstructionsAt` / `sliceWord` / key gate
- Example：`Examples.InstructionsSlice` digest `fa750f0ebf227df3`
- Lean：`Tests.InstructionsSliceSpec`
- Mollusk：`instructions_slice` 3/3（full window + short + wrong key fail closed）
