---
id: svm-rt-005
track: B-runtime
status: todo
plan: ../svm-work-plan.md
priority: F0/F1
---

# svm-rt-005 nested / wide dynamic return 政策

## 目标

在现有 top-level one-limb bounded/tagged return 之上，定义仍有界的 nested/constructed/wide return 政策（若仍落在 v1 ceiling）。

## 交付

1. schema/budget 规则写清
2. SVM Borsh 独立 binding
3. 超预算 / 非法嵌套 fail closed

## 非目标

无界动态图；与 EVM 物理 layout 统一。
