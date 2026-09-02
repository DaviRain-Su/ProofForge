---
id: svm-sem-124
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-123]
---

# svm-sem-124 L3/E∞ knife 119 — Loader account-16 owner limbs 2/3 after skip chain

## 目标

Knife 118 lands account-16 owner lo. Emit then loads account-16 owner limbs 2/3.

## 交付

1. `account16OwnerHiInputMem` / `walkAccount16OwnerHiAfterSkipChain?` /
   `evalWalkAccount16OwnerHiAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `owner hi` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 119 section
- Spec guards for account-16 owner hi vs abs loads after sedecuple skip

## 仍未覆盖

account-16 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
