---
id: svm-eng-002
track: F-eng
status: done
plan: ../svm-work-plan.md
depends-on: [svm-eng-001]
---

# svm-eng-002 SVM 能力 + 证明双矩阵收口页

## 目标

单页声明：能力矩阵（runtime-sdk / parity）与形式化矩阵（sf-*）的当前状态。

## 交付

1. [`docs/plan/svm-status-matrix.md`](../svm-status-matrix.md) — capability + formalization + L3 + eng board
2. [`scripts/svm_status_summary.py`](../../../scripts/svm_status_summary.py) — task front-matter status board
3. Synced with [`svm-work-plan.md`](../svm-work-plan.md) §6 / [`README.md`](../README.md)

## 非目标

自动把 capability-matrix 行改写成证明状态；WASM PR 状态。
