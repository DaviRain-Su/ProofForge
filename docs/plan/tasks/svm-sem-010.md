---
id: svm-sem-010
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-009]
---

# svm-sem-010 L3/E∞ knife 5 — Loader account-0 lamports/data_len

## 目标

在 `svm-sem-009` account-0 flag walk 之上，覆盖 Emit 对 account-0 的
`ACC0_LAMPORTS`（`0x50`）与 `ACC0_DATA_LEN`（`0x58`）：同一 `r8` header 游标
`ldxdw` 两字，并与绝对 `r6`-相对加载一致。

## 交付

1. `account0BudgetInputMem` / `walkAccount0Budget?` / `evalWalkAccount0BudgetToStack?` /
   `evalAbsAccount0Budget?`
2. Theorems：`walkAccount0Budget_verified`、`evalWalkAccount0_lamports_1000_dataLen_128`、
   `walkAccount0Budget_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 5 section
- Spec guards for lamports=`1000` / data_len=`128` vs abs loads

## 仍未覆盖

owner limbs；完整 account 向量 walk；syscall/CPI/sysvar；ELF accept。
