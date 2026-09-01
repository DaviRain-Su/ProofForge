---
id: svm-sem-080
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-079]
---

# svm-sem-080 L3/E∞ knife 75 — Loader account-10 lamports/data_len after skip chain

## 目标

Knife 74 covers account-10 signer/writable. Emit then reads account-10 lamports and data_len.

## 交付

1. `account10BudgetInputMem` / `walkAccount10BudgetAfterSkipChain?` /
   `evalWalkAccount10BudgetAfterSkipChainToStack?` / `evalAbsAccount10Budget?`
2. Theorems：`walkAccount10BudgetAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_lamports_10000_dataLen_208`、
   `walkAccount10BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 75 section
- Spec guards for lamports=10000/dataLen=208 vs abs loads

## 仍未覆盖

account-10 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
