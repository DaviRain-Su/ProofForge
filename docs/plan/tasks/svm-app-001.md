---
id: svm-app-001
track: D-app
status: done
plan: ../svm-work-plan.md
---

# svm-app-001 Phoenix-v1 下一组 instruction

## 目标

在 `Examples` 内用现有 SDK 组合下一组 Phoenix-v1 官方 instruction；不扩 Ops/IR/Emit。

## 交付

1. 指令语义与账户合同 — **done**：tags **10/11** `CancelMultipleOrdersById` /
   `CancelMultipleOrdersByIdWithFreeFunds`（官方 Borsh `Vec<CancelOrderParams>`；本 profile
   片 **capacity = 1**；空 vec noop；side/MSB/missing/foreign skip；10=withdraw / 11=free）
2. Mollusk 正反例 — **done**：`phoenix_v1_profile.rs` empty / success / skip / withdraw /
   noncanonical / storage+token reject
3. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm` — **done**：digest `2dc1e143994eca61`；
   Spec adapter+composition+ASM routes 8–11；capacity 见 [svm-app-004](svm-app-004.md)

## 非目标

把 matching 策略下沉到 SDK。
