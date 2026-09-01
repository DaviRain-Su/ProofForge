---
id: svm-sdk-003
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1
depends-on: []
---

# svm-sdk-003 generic POD transient record shapes

## 目标

在 Record64 / Vector128 / Vector256 之后，增加下一组仍 allocation-free 的 POD transient 形状（例如更多 limb 组合或固定 schema record），复用现有 bump lifecycle。

## 交付

1. 仅 SDK 组合，无新 Runtime leaf（除非证明不够）
2. 双 slot 隔离保留
3. 双 consumer；落地后挂形式化跟踪

## 非目标

泛型任意 POD 反射；持久化到 account。
