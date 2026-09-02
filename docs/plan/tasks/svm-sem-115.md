---
id: svm-sem-115
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-114]
---

# svm-sem-115 L3/E∞ knife 110 — Loader account-15 lamports/data_len after skip chain

## 目标

Knife 109 completes account-15 flags after the skip chain. Emit then reads lamports and data_len.

## 交付

1. `account15BudgetInputMem` / `walkAccount15BudgetAfterSkipChain?` /
   `evalWalkAccount15BudgetAfterSkipChainToStack?` / `evalAbsAccount15Budget?`
2. Theorems + Spec `#guard`s for lamports=15000/dataLen=288

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 110 section

## 仍未覆盖

account-15 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
