---
id: svm-sem-083
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-082]
---

# svm-sem-083 L3/E∞ knife 78 — Loader account-10 executable/rent after skip chain

## 目标

Knife 77 completes account-10 owner pubkey. Emit then reads executable and rent_epoch.

## 交付

1. `account10ExecRentInputMem` / `walkAccount10ExecRentAfterSkipChain?` /
   `evalWalkAccount10ExecRentAfterSkipChainToStack?` / `evalAbsAccount10ExecRent?`
2. Theorems：`walkAccount10ExecRentAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_executable_1_rent_0xF5`、
   `walkAccount10ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 78 section
- Spec guards for executable=1/rent=0xF5 vs abs loads

## 仍未覆盖

account-10→account-11 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
