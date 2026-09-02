---
id: svm-sem-129
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-128]
---

# svm-sem-129 L3/E∞ knife 124 — Loader account-17 lamports/data_len after skip chain

## 目标

Knife 123 lands account-17 flags. Emit then loads account-17 lamports/data_len.

## 交付

1. `account17BudgetInputMem` / `walkAccount17BudgetAfterSkipChain?` /
   `evalWalkAccount17BudgetAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS budget constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 124 section
- Spec guards for account-17 lamports/data_len vs abs loads after septendecuple skip

## 仍未覆盖

account-17 owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
