---
id: svm-sdk-005
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F2
depends-on: [svm-rt-002]
---

# svm-sdk-005 Token-2022 extension Sdk facade

## 目标

把 svm-rt-002 的 extension 语义收成 `Svm.Sdk` 可组合 facade；应用不直连 Runtime leaf。

## 交付

1. typed view + effect wrappers
2. classic Token 路径不受影响
3. 未知 extension 仍拒绝

## 非目标

Emit 里出现 extension 专用 recipe 名。
