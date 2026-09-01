---
id: svm-sdk-007
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1/F2
---

# svm-sdk-007 持久容器有界 insert/remove/iteration

## 目标

在现有 Map/Set/Vec/Queue 上提供有界 iteration / 批量删除等 API，不引入 heap iterator 对象。

## 交付

1. 编译期 capacity 内的游标或 index scan
2. 与形式化模型可对齐的语义
3. 双 consumer

## 非目标

`for (x in map)` 无界语法糖；跨账户指针。
