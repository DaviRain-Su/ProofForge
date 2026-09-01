---
id: svm-sem-001
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E1
depends-on: []
---

# svm-sem-001 L3/E1 — operand materialization + straightline

## 背景

`solanalib` 与 `sbpfSemantics` 已接入。E0 已有 checked arith / store / branch fragment
correspondence。本片把「操作数怎么进寄存器」和「多指令直线序列」补上。

## 目标

对真实 Counter（或等价最小例）的一段 emit：

1. operand materialization 与 Solanalib 寄存器约定对齐  
2. 多指令 straightline 在 `step` 下可模拟  
3. 与 source checked guard 成功/失败边一致  

## 交付

- `ProofForge/Svm/Solanalib.lean`（或邻接模块）新增定理  
- `#print axioms` 合格  
- 文档注明覆盖的 emit 形状与故意未覆盖点  

## 非目标

整函数 CFG（E3）、账户字模型桥（E4）、Agave 主机（E∞）。
