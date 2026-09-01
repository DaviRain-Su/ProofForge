---
id: svm-sem-108
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-107]
---

# svm-sem-108 L3/E∞ knife 103 — Loader account-14 lamports/data_len after skip chain

## 目标

Knife 102 completes account-14 flags after the skip chain. Emit then reads lamports and data_len。

## 交付

1. `account14BudgetInputMem` / `walkAccount14BudgetAfterSkipChain?` /
   `evalWalkAccount14BudgetAfterSkipChainToStack?` / `evalAbsAccount14Budget?`
2. Theorems：`walkAccount14BudgetAfterSkipChain_verified`、`evalWalkAccount14_after_skip_lamports_14000_dataLen_272`、`walkAccount14BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 103 section
- Spec guards for lamports=14000/dataLen=272 vs abs loads

## 仍未覆盖

account-14 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
