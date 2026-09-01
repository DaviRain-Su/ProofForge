---
id: svm-sem-005
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E5
depends-on: [svm-sem-004, sf-002]
---

# svm-sem-005 L3/E5 — 选定容器全函数有界证明

## 目标

选一个已有 L2 模型的容器路径（**建议 Queue empty-push**，与 `sf-001/002` 对齐），
完成「source → 模型代数 → emit → Solanalib 步进」有界全函数证明。

## 交付

1. 与 Track A 同一 `BoundedQueue` / 模型主语  
2. empty-push（或选定路径）在 sBPF 语义下读回与模型一致  
3. 写清还剩哪些 Queue 分支未进 L3  

## 非目标

Phoenix 全指令 L3；E∞ 主机；一次性覆盖所有 SDK 表面。
