---
id: svm-sem-094
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-093]
---

# svm-sem-094 L3/E∞ knife 89 — Loader account-12 lamports/data_len after skip chain

## 目标

Knife 88 completes account-12 flags after the skip chain. Emit then reads lamports and data_len。

## 交付

1. `account12BudgetInputMem` / `walkAccount12BudgetAfterSkipChain?` /
   `evalWalkAccount12BudgetAfterSkipChainToStack?` / `evalAbsAccount12Budget?`
2. Theorems：`walkAccount12BudgetAfterSkipChain_verified`、`evalWalkAccount12_after_skip_lamports_12000_dataLen_240`、`walkAccount12BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 89 section
- Spec guards for lamports=12000/dataLen=240 vs abs loads

## 仍未覆盖

account-12 owner/exec-rent。
