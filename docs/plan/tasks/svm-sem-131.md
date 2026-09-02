---
id: svm-sem-131
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-130]
---

# svm-sem-131 L3/E∞ knife 126 — Loader account-17 owner limbs 2/3 after skip chain

## 目标

Knife 125 lands account-17 owner lo. Emit then loads account-17 owner limbs 2/3.

## 交付

1. `account17OwnerHiInputMem` / `walkAccount17OwnerHiAfterSkipChain?` /
   `evalWalkAccount17OwnerHiAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS owner-hi constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 126 section
- Spec guards for account-17 owner hi vs abs loads after septendecuple skip

## 仍未覆盖

account-17 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
