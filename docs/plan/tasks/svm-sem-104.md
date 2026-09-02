---
id: svm-sem-104
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-103]
---

# svm-sem-104 L3/E∞ knife 99 — Loader account-13 executable/rent after skip chain

## 目标

Knife 98 completes account-13 owner pubkey after the skip chain. Emit then reads account-13
executable（header+3）and rent_epoch。

## 交付

1. `account13ExecRentInputMem` / `walkAccount13ExecRentAfterSkipChain?` /
   `evalWalkAccount13ExecRentAfterSkipChainToStack?` / `evalAbsAccount13ExecRent?`
2. Theorems：`walkAccount13ExecRentAfterSkipChain_verified`、`evalWalkAccount13_after_skip_executable_1_rent_0xF8`、`walkAccount13ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 99 section
- Spec guards for executable=1/rent=0xF8 vs abs loads

## 仍未覆盖

account-13→account-14 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
