---
id: svm-sem-125
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-124]
---

# svm-sem-125 L3/E∞ knife 120 — Loader account-16 executable/rent after skip chain

## 目标

Knife 119 lands account-16 owner hi. Emit then loads account-16 executable/rent_epoch.

## 交付

1. `account16ExecRentInputMem` / `walkAccount16ExecRentAfterSkipChain?` /
   `evalWalkAccount16ExecRentAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `executable/rent` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 120 section
- Spec guards for account-16 executable/rent vs abs loads after sedecuple skip

## 仍未覆盖

account-16→account-17 skip — see [svm-sem-126](svm-sem-126.md)；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
