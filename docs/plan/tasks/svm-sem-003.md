---
id: svm-sem-003
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E3
depends-on: [svm-sem-001, svm-sem-002]
---

# svm-sem-003 L3/E3 — Counter 整函数有界 CFG correspondence

## 目标

把 Counter `increment`（或同级单入口）从 source CFG → emit → Solanalib `step*`
做成 **整函数、有界 block** 的 end-to-end correspondence。

## 交付

1. success 路径：guard 过 → body → store → 返回约定 — **done**
2. overflow / 失败路径：在 store 前离开，内存不变 — **done**
3. 明确 block/指令数上界；超出 fail closed 或拆片 — **done**（≤3 blocks，≤64 instr）

## Evidence

- `ProofForge/Svm/Solanalib.lean` E3：`counterIncrementCFG?` / `evalCounterIncrementCFG`
- Theorems: `counterIncrementCFG_within_bounds`, `evalCounterIncrementCFG_add_7_5`,
  `evalCounterIncrementCFG_overflow_max` (`native_decide`; axioms `propext`/`Quot.sound`)
- `Tests/SolanalibSpec.lean` E3 `#guard`s for bounds / success 7+5 / overflow max+1
- Layout: entry (materialize+guard+ALU+scratch+ja) → success (reload+store+r0=0) |
  overflow (r0=0x1001); no Phoenix/Agave ELF claim

## 依赖

E1 materialization；E2 golden 用于回归。

## 非目标

多入口程序（E5）；syscall/CPI（E∞）；与 Agave 字节级 ELF 一致。
