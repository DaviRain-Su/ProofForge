---
id: svm-sdk-002
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1
---

# svm-sdk-002 owner-reassign 生命周期政策

## 目标

对 program-owned account 的 owner 再赋值：要么提供 checked facade，要么在能力矩阵标 `n/a` 并永久 fail closed——禁止半开。

## 交付

1. 书面政策 + 实现或显式拒绝测试
2. 若实现：权限/可写/余额/alias 前置条件齐全

## 非目标

任意账户类型的静默 owner 修改。
