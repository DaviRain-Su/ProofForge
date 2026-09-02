---
id: svm-sem-122
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-121]
---

# svm-sem-122 L3/E∞ knife 117 — Loader account-16 lamports/data_len after skip chain

## 目标

Knife 116 lands account-16 flags. Emit then loads account-16 lamports/data_len.

## 交付

1. `account16BudgetInputMem` / `walkAccount16BudgetAfterSkipChain?` /
   `evalWalkAccount16BudgetAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `lamports/data_len` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 117 section
- Spec guards for account-16 lamports/data_len vs abs loads after sedecuple skip

## 仍未覆盖

account-16 owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
