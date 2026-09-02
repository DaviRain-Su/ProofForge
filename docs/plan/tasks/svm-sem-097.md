---
id: svm-sem-097
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-096]
---

# svm-sem-097 L3/E∞ knife 92 — Loader account-12 executable/rent after skip chain

## 目标

Knife 91 completes account-12 owner pubkey after the skip chain. Emit then reads account-12
executable（header+3）and rent_epoch。

## 交付

1. `account12ExecRentInputMem` / `walkAccount12ExecRentAfterSkipChain?` /
   `evalWalkAccount12ExecRentAfterSkipChainToStack?` / `evalAbsAccount12ExecRent?`
2. Theorems：`walkAccount12ExecRentAfterSkipChain_verified`、`evalWalkAccount12_after_skip_executable_1_rent_0xF7`、`walkAccount12ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 92 section
- Spec guards for executable=1/rent=0xF7 vs abs loads

## 仍未覆盖

account-12→account-13 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
