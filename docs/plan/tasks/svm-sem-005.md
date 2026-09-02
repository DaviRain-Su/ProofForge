---
id: svm-sem-005
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E5
depends-on: [svm-sem-004, sf-002]
---

# svm-sem-005 L3/E5 — 选定容器全函数有界证明

## 目标

选一个已有 L2 模型的容器路径（**Queue empty-push**，与 `sf-001/002` 对齐），
完成「source → 模型代数 → emit → Solanalib 步进」有界全函数证明。

## 交付

1. 与 Track A 同一 `BoundedQueue` / 模型主语 — **done**（TicketLine 布局刀）
2. empty-push 在 sBPF 语义下读回与模型一致 — **done**（E4 bridge 投影 + 三写 storev）
3. 写清还剩哪些 Queue 分支未进 L3 — **done**

## Evidence

- `ProofForge/Svm/Solanalib.lean` E5：`demoQueue` / `demoEmptyPushAw` /
  `projectDemoEmptyPush?` / `demoEmptyPushStores?`
- Geometry: `demoQueue_wellFormed`, `demoQueue_fieldWords` (head@2, count@3, slot1@4)
- Model: `demoEmptyPush_model_readback`
- L3: `projectDemoEmptyPush_loads`, `demoEmptyPushStores_loads`,
  `projectDemoEmptyPush_eq_stores` (`native_decide`)
- `Tests/SolanalibSpec.lean` E5 `#guard`s

## 仍未进 L3 的 Queue 分支

- push：full / nowrap 非空 / wrap
- pop：clear / advance / wrap
- peek / initialize 全路径
- TicketLine 整程序 emit→step（仅 empty-push 写集桥）
- Agave/ELF / walked `r7`

## 非目标

Phoenix 全指令 L3；E∞ 主机；一次性覆盖所有 SDK 表面。
