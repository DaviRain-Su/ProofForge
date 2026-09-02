---
id: svm-sem-111
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-110]
---

# svm-sem-111 L3/E∞ knife 106 — Loader account-14 executable/rent after skip chain

## 目标

Knife 105 completes account-14 owner pubkey after the skip chain. Emit then reads account-14
executable（header+3）and rent_epoch。

## 交付

1. `account14ExecRentInputMem` / `walkAccount14ExecRentAfterSkipChain?` /
   `evalWalkAccount14ExecRentAfterSkipChainToStack?` / `evalAbsAccount14ExecRent?`
2. Theorems：`walkAccount14ExecRentAfterSkipChain_verified`、`evalWalkAccount14_after_skip_executable_1_rent_0xF9`、`walkAccount14ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 106 section
- Spec guards for executable=1/rent=0xF9 vs abs loads

## 仍未覆盖

account-14→account-15 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
