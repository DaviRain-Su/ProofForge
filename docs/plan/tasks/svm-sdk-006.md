---
id: svm-sdk-006
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1/F2
---

# svm-sdk-006 UTF-8 Memo + richer migration payload

## 目标

1. Memo：在 ASCII 之外提供 strict UTF-8 bounded facade（或明确拒绝并写 n/a）
2. Versioned：更丰富的 payload migration 边（仍单边显式）

## 交付

1. UTF-8 Memo facade — **done**
   - `ProofForge.Svm.Memo.Utf8`：`maxBytes := 512`、strict UTF-8 `bytesWellFormed` / `wellFormed`
   - `ProofForge.Svm.Sdk.Memo.Utf8.write`：同 Ascii CPI geometry；emit 走 UTF-8 bytes
   - Ops / Extract Memo 几何同时接受 Ascii 与 Utf8
2. Payload migration edge — **done**
   - `ProofForge.Svm.Sdk.Versioned.PayloadTransition`：单边 copy-one-word + bump version；无多跳图
3. 正反例 — **done**
   - `Examples.MemoUtf8` digest `c13eb931ded2755a`（`"café"`）
   - `Examples.VersionedPayloadMigrator` digest `39327e5abe0c9299`

## 验收证据

- Lean：`Tests.MemoUtf8Spec`、`Tests.SvmVersionedCodecSpec`、`Tests.SvmSdkProgramSpec`（λ OK；513-byte fail-closed）
- Mollusk：`memo_utf8` 2/2；`versioned_codec` 5/5（含 payload migration）

## 非目标

隐式多边 migration 图；runtime-selected Memo account geometry（仍 F1/F2 后续）。
