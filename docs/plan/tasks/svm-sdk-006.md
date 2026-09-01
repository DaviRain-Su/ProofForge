---
id: svm-sdk-006
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1/F2
---

# svm-sdk-006 UTF-8 Memo + richer migration payload

## 目标

1. Memo：在 ASCII 之外提供 strict UTF-8 bounded facade（或明确拒绝并写 n/a）
2. Versioned：更丰富的 payload migration 边（仍单边显式）

## 交付

正反例；短/非法 UTF-8 fail closed；migration 不隐式多边图。
