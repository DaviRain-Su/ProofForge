---
id: svm-sem-003
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E3
depends-on: [svm-sem-001, svm-sem-002]
---

# svm-sem-003 L3/E3 — Counter 整函数有界 CFG correspondence

## 目标

把 Counter `increment`（或同级单入口）从 source CFG → emit → Solanalib `step*`
做成 **整函数、有界 block** 的 end-to-end correspondence。

## 交付

1. success 路径：guard 过 → body → store → 返回约定  
2. overflow / 失败路径：在 store 前离开，内存不变  
3. 明确 block/指令数上界；超出 fail closed 或拆片  

## 依赖

E1 materialization；E2 golden 用于回归。

## 非目标

多入口程序（E5）；syscall/CPI（E∞）；与 Agave 字节级 ELF 一致。
