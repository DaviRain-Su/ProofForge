---
id: svm-sdk-007
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1/F2
---

# svm-sdk-007 持久容器有界 insert/remove/iteration

## 目标

在现有 Map/Set/Vec/Queue 上提供有界 iteration / 批量删除等 API，不引入 heap iterator 对象。

## 交付

1. 编译期 capacity 内的 index scan — **done**
   - `StorageEnumerableSet.Descriptor.valueAt` / `canIndex` / `removeAt` / `clear`
   - `BoundedQueue.getAt` / `clear`
   - `BoundedVec.clear` / `removeAt`
2. 与形式化模型可对齐的语义 — **done**
   - `StorageEnumerableSetModel.EnumSet.removeAt` / `.clear`
   - `StorageModel.mQueueGetAt` / `mQueueClear`
3. 双 consumer — **done**
   - `MemberDirectory`: capacity-4 `valueAt` scan + `removeAt` + `clearStorage`
   - `UniqueRoster`: capacity-5 `identityAt` scan + `clearRoster`
   - `TicketLine`: `lineGetAt` + `lineClear`（Queue index scan）

## 验收证据

- Lean：`Tests.SvmSdkStorageEnumerableSetSpec`、`Tests.SvmSdkQueueSpec`
- Digests：`MemberDirectory` `22c051a109d012b5`；`UniqueRoster` `6857a73c4f999356`；`TicketLine` `11b8e19a66200ed7`
- Mollusk：`storage_enumerable_set` 7/7；`ticket_line` 3/3

## 非目标

`for (x in map)` 无界语法糖；跨账户指针；heap iterator 对象；in-program fold over account reads（consumer 侧 capacity-bounded `valueAt`/`identityAt`/`getAt` scan）。
