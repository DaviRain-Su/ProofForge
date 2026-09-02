---
id: svm-sem-132
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-131]
---

# svm-sem-132 L3/E∞ knife 127 — Loader account-17 executable/rent after skip chain

## 目标

Knife 126 lands account-17 owner hi. Emit then loads account-17 executable/rent_epoch.

## 交付

1. `account17ExecRentInputMem` / `walkAccount17ExecRentAfterSkipChain?` /
   `evalWalkAccount17ExecRentAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS `executable/rent` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 127 section
- Spec guards for account-17 executable/rent vs abs loads after septendecuple skip

## 仍未覆盖

account-17→account-18 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
