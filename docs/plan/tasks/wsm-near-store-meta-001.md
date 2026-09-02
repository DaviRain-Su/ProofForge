---
id: wsm-near-store-meta-001
scope: near
status: todo
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

## 第一切片（Vector only）

1. `Vector.Handle`（或等价命名）绑定 `Prefix4` + capacity
2. Example：`Examples/NearVector.lean` 经 Handle 读写，不再直接传 raw prefix / `ResultBuffer` 拼装
3. IR digest pin + `runtime-tests/near/vector.py` 仍绿
4. 更新 `capability-matrix.md` §5 / `analysis/near-runtime-sdk.md` N5 行

## 非目标（本 task）

- Queue / Iterable / TreeMap Handle
- 通用 `T`、Sha256 键
- N>8 `andN`、N15 digest 表
- near-sdk Drop 语义

## 验收

N14 行 → done（至少 Vector Handle + golden/sandbox）；其余集合可开 follow-up 切片。
