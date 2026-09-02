---
id: wsm-near-store-meta-001
scope: near
status: done
depends-on: [wsm-near-state-envelope-001, wsm-near-vector-001]
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# wsm-near-store-meta-001 — collection prefix/metadata Handle（N14）

## 目标

为 NEAR Store 集合提供 **source 级 Handle**：绑定 compile-time `Prefix4` + capacity，
并把 **length / head 等可变元数据** 明确归到 **N9 STATE 字段**（不写第二把 KV length key，
不冒充 near-sdk `Drop` / `IndexMap` cache）。

## 决策（相对既有 Vector 面）

| 项 | 选择 |
|---|---|
| 前缀 | compile-time `Prefix4`，由 `Handle` 携带；examples 不再手写 raw tag |
| length | 留在 `State` 字段（N9 envelope）；**不是** `prefix ‖ "len"` 持久键 |
| 元素键 | 保持现状：`VEC1 ‖ u32_le(index)` + Borsh u64 |
| Drop/cache | **不做**；文档写 compatibility diff |

## 第一切片（Vector only）— landed

1. `DirectVector64.Handle` 绑定 `Prefix4` + capacity（`ProofForge/Wasm/Near/Sdk/Store/Vector.lean`）
2. `Examples/NearVector.lean` 经 `@[pf_inline] slots` Handle 读写（不再在 entry 手写 raw prefix）
3. Extract：`reduceCtorProjection?` 允许 `ProofForge.Wasm.Near.Sdk.Store.*` 投影，使
   `Handle.capacity` / `Handle.tag` 在 `@[pf_inline]` 下擦除为字面量
4. IR digest **unchanged** `cd60fb0f3ce40ade`（Handle 为零成本 facade）；`Tests/NearVectorSpec`
   绿；registry pin 不变

## Follow-up（Queue Handle）— landed 2026-09-02

1. `DirectQueue64.Handle`（capacity + `Prefix4`）；`head`/`length` 仍在 STATE
2. `Examples/NearQueue.lean` 经 `@[pf_inline] slots`；digest **unchanged** `a8bf10c3476ef45f`
3. Lookup Map/Set Handle landed (`d14778ca02c69012` unchanged); Iterable Handle landed (`98d132f8e2c7cd5c` unchanged)

## Follow-up（Iterable Handle）— landed 2026-09-02

1. `DirectIterableMap64.Handle` / `DirectIterableSet64.Handle`（capacity + literal `vectorTag`/`lookupTag`）
2. `Examples/NearIterable.lean` 经 `@[pf_inline] mapSlots` / `setSlots`；digest **unchanged** `98d132f8e2c7cd5c`
3. Extract 需 literal `Prefix4` tag（非 `Prefix3` 派生），与 Vector `Handle.tag` 同模式

## 非目标（本 task / follow-up）

- TreeMap Handle
- 通用 `T`、Sha256 键
- N>8 `andN`、N15 digest 表
- near-sdk Drop 语义

## 验收

N14 行 → **done**（Vector + Queue + Lookup + Iterable Handle；golden digest 稳定）。
