---
id: svm-sem-001
track: E-l3
status: done
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

1. `ProofForge/Svm/Solanalib.lean` — `materializeOperand?` / `checkedStraightlineFragment?` /
   `evalCounterStraightline` + theorems
2. `#print axioms`：`propext` / `Quot.sound` / `native_decide` only
3. `Tests/SolanalibSpec.lean` E1 `#guard`s；`docs/modules/solanalib.md` 覆盖形状

## Evidence

- Counter field+arg / field+lit assembly well-formed
- Concrete add `7+5 → 12` success and `max+1` overflow via materialize → E0 CFG write
- Walked `r7` args, whole-function CFG, AccountWords bridge remain out of scope

## 非目标

整函数 CFG（E3）、账户字模型桥（E4）、Agave 主机（E∞）。
