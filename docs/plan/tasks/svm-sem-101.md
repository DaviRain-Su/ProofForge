---
id: svm-sem-101
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-100]
---

# svm-sem-101 L3/E∞ knife 96 — Loader account-13 lamports/data_len after skip chain

## 目标

Knife 95 completes account-13 flags after the skip chain. Emit then reads lamports and data_len。

## 交付

1. `account13BudgetInputMem` / `walkAccount13BudgetAfterSkipChain?` /
   `evalWalkAccount13BudgetAfterSkipChainToStack?` / `evalAbsAccount13Budget?`
2. Theorems：`walkAccount13BudgetAfterSkipChain_verified`、`evalWalkAccount13_after_skip_lamports_13000_dataLen_256`、`walkAccount13BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 96 section
- Spec guards for lamports=13000/dataLen=256 vs abs loads

## 仍未覆盖

account-13 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
