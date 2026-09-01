---
id: svm-sdk-004
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1
---

# svm-sdk-004 更多 manifest-bounded transient handles

## 目标

若需要 >2 同类型 slot，先扩 resource manifest，再开放额外 compile-time handles；默认仍保持 2。

## 交付

1. manifest 先行
2. 生命周期/OOM 语义与现有一致
3. CI 防泄漏

## 非目标

运行时动态 slot 数量。
