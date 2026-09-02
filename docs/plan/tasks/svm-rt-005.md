---
id: svm-rt-005
track: B-runtime
status: done
plan: ../svm-work-plan.md
priority: F0/F1
---

# svm-rt-005 nested / wide dynamic return 政策

## 目标

在现有 top-level one-limb bounded/tagged return 之上，定义仍有界的 nested/constructed/wide return 政策（若仍落在 v1 ceiling）。

## 交付

1. schema/budget 规则写清 — `ReturnBudget` / `returnBudget` in `ProofForge/Svm/EntryAdapter.lean`
2. SVM Borsh 独立 binding — wide scalar / nested-static element leaves via `staticBorshLeaves`; Extract limb offsets + Option `slot_p0` / `slot_p0_w{n}`
3. 超预算 / 非法嵌套 fail closed — capacity/wire/scratch ceilings; dynamic-in-dynamic rejected

## Evidence

- RawEntry digest `243ea72de353e8e3` (tags 27 `echoBoundedU128`, 29 `echoOptionU128`)
- `Tests/EntryAdapterSpec.lean` decode + CFG + asm
- Mollusk `wide_dynamic_returns_publish_multi_limb_borsh_prefixes`
- Product-element Extract projection deferred (schema decode still accepted for tuple elements)

## 非目标

无界动态图；与 EVM 物理 layout 统一；Vec-of-Option / record-with-bounded return.
