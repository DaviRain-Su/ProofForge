---
id: svm-rt-001
track: B-runtime
status: done
plan: ../svm-work-plan.md
priority: F1
---

# svm-rt-001 Clock signed timestamp 视图

## 目标

在已有 unsigned/Bool Clock 字段之外，提供 **signed** timestamp 视图，布局与官方 sysvar 一致；错误宽度/偏移 fail closed。

## 交付

1. target-owned Sysvar 查询叶 + SDK facade — **done**
   - `ClockField.epochStartTimestamp` @ native offset 8（官方 `i64`）
   - `Runtime.clockEpochStartTimestamp` / `Sdk.Sysvar.Clock.epochStartTimestamp`
   - `unixTimestamp` 文档改为原生 `i64` 位型（仍由 `UInt64` 承载）
   - `Clock.asSigned`：Lean 侧二补码 `Int` 视图（不抽出）
2. 与现有 unsigned 字段共存；slot/epoch/leader 偏移不变 — **done**
3. Examples.Clock 增加 `epochStart` / `unix`；Mollusk 覆盖正/负边界 — **done**
4. Lean：`Tests.SvmSdkSysvarSpec` / `Tests.ClockSpec` 绿；Registry digest 更新 — **done**

## 证据

- Extracted IR digest：`19039a4899e65b6d`（原 `e55d1f77fe147ef7`）
- ELF：4256 bytes；SHA-256 `b6ea421b78873313689b7805f355bc70fc0451843a9bc2f925f6df63d2c741df`
- Asm SHA-256 `6d925416935a547578b083d5c4fbd4d2fc4fbf29665ef419591bff254da66e92`
- Mollusk Clock：12/12（含负 `unix_timestamp` / `epoch_start_timestamp`）
- `check_no_sorry` / `check_ownership` 绿

## 非目标

通用任意 sysvar 切片；Instructions sysvar（见 svm-rt-004）；抽出路径上的 `Int64` 源类型。
