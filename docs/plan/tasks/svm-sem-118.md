---
id: svm-sem-118
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-117]
---

# svm-sem-118 L3/E∞ knife 113 — Loader account-15 executable/rent after skip chain

## 目标

Knife 112 completes account-15 owner pubkey after the skip chain. Emit then reads account-15 executable (header+3) and rent.

## 交付

1. `account15ExecRentInputMem` / `walkAccount15ExecRentAfterSkipChain?` /
   `evalWalkAccount15ExecRentAfterSkipChainToStack?` / `evalAbsAccount15ExecRent?`
2. Theorems：`walkAccount15ExecRentAfterSkipChain_verified`、`evalWalkAccount15_after_skip_executable_1_rent_0xFA`、`walkAccount15ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 113 section
- Spec guards for executable=1/rent=0xFA vs abs loads

## 仍未覆盖

account-15→account-16 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
