---
id: svm-sem-087
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-086]
---

# svm-sem-087 L3/E∞ knife 82 — Loader account-11 lamports/data_len after skip chain

## 目标

Knife 81 covers account-11 signer/writable after the skip chain. Emit then reads account-11
lamports and data_len（`+0x48` / `+0x50`）。

## 交付

1. `account11BudgetInputMem` / `walkAccount11BudgetAfterSkipChain?` /
   `evalWalkAccount11BudgetAfterSkipChainToStack?` / `evalAbsAccount11Budget?`
2. Theorems：`walkAccount11BudgetAfterSkipChain_verified`、`evalWalkAccount11_after_skip_lamports_11000_dataLen_224`、`walkAccount11BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 82 section
- Spec guards for lamports=11000/dataLen=224 vs abs loads

## 仍未覆盖

account-11 owner/exec-rent。
