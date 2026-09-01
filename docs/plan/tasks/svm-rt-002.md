---
id: svm-rt-002
track: B-runtime
status: todo
plan: ../svm-work-plan.md
priority: F2
depends-on: []
---

# svm-rt-002 Token-2022 第一个 typed extension 语义

## 目标

在已有 TLV envelope（未知 extension 原子拒绝）上，开放 **一个** 完整 typed extension 语义。

建议优先：`transfer-fee` **或** `mint-close-authority`（选更容易做双 consumer 的）。

## 交付

1. 有界解析 + 状态视图 + 必要 CPI/状态更新语义
2. 两个非 Phoenix consumer
3. 未建模 extension 继续 fail closed
4. 不把 extension 名写进通用 Emit

## 非目标

一次做完所有 Token-2022 extension。
