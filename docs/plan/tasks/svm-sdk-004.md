---
id: svm-sdk-004
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1
depends-on: []
---

# svm-sdk-004 更多 manifest-bounded transient handles

## 目标

若需要 >2 同类型 slot，先扩 resource manifest，再开放额外 compile-time handles；默认仍保持 2。

## 交付

1. manifest 先行 — `Sdk.Transient.ResourceManifest` / `defaultManifest`；`wellFormed` 拒绝 `> maxHandleSlots`
2. Vector64 / Bytes `Config.wellFormed` 经 `admitsVectorSlot` / `admitsBytesSlot` 门控；生命周期/OOM 语义与现有双 slot 一致（无第三 live bank）
3. CI 防泄漏 — Lean env guard 禁止半开第三 slot facade（`boundedAlt2` 等）

## 非目标

运行时动态 slot 数量；本片不 remap deep-scratch、不落地第三个 live handle。

## 证据

- Lean: `ProofForge/Svm/Sdk/Transient.lean`（ResourceManifest）；`TransientVec`/`TransientBytes` Config gates；`Tests/SvmTransientResourceManifestSpec.lean`
- Follow-up: scratch relayout 后再把 manifest `vectorSlots`/`bytesSlots` >2 标为 well-formed 并开放 handles
