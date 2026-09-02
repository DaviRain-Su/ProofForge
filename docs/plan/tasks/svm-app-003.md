---
id: svm-app-003
track: D-app
status: done
plan: ../svm-work-plan.md
---

# svm-app-003 非 Phoenix SDK 小例子集

## 目标

为 Queue / Map / BitSet / Versioned 各提供一个最小非 Phoenix example，证明组件可复用。

## 交付

Mollusk；可选 Surfpool 部署一门面例子 — **done**（Mollusk required；Surfpool optional deferred）

## Evidence

- Queue+Map: `Examples.TicketLine` + Mollusk `ticket_line` (3)
- Set/Map-family: `Examples.UniqueRoster` + Mollusk `storage_enumerable_set` (7)
- BitSet: `Examples.FeatureBits`/`ClaimBits` + Mollusk `storage_bit_set` (3)
- Versioned: `Examples.VersionedLedger` + Mollusk `versioned_codec` (5)
- Index: `docs/modules/sdk-mini-examples.md`
- Registry digests already pinned for all five programs

## 非目标

Surfpool 公网部署；Phoenix 指令面；新增 SDK 原语。
