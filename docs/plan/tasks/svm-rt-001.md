---
id: svm-rt-001
track: B-runtime
status: todo
plan: ../svm-work-plan.md
priority: F1
---

# svm-rt-001 Clock signed timestamp 视图

## 目标

在已有 unsigned/Bool Clock 字段之外，提供 **signed** timestamp 视图，布局与官方 sysvar 一致；错误宽度/偏移 fail closed。

## 交付

1. target-owned Sysvar 查询叶或等价 facade 字段
2. 与现有 unsigned 字段共存；不破坏已有 digest
3. Mollusk 覆盖正常值与边界；Lean 回归绿

## 非目标

通用任意 sysvar 切片；Instructions sysvar（见 svm-rt-004）。
