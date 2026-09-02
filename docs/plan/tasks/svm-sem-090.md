---
id: svm-sem-090
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-089]
---

# svm-sem-090 L3/E∞ knife 85 — Loader account-11 executable/rent after skip chain

## 目标

Knife 84 completes account-11 owner pubkey after the skip chain. Emit then reads account-11
executable（header+3）and rent_epoch。

## 交付

1. `account11ExecRentInputMem` / `walkAccount11ExecRentAfterSkipChain?` /
   `evalWalkAccount11ExecRentAfterSkipChainToStack?` / `evalAbsAccount11ExecRent?`
2. Theorems：`walkAccount11ExecRentAfterSkipChain_verified`、`evalWalkAccount11_after_skip_executable_1_rent_0xF6`、`walkAccount11ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 85 section
- Spec guards for executable=1/rent=0xF6 vs abs loads

## 仍未覆盖

account-11→account-12 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
