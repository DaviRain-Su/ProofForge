---
id: svm-sem-130
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-129]
---

# svm-sem-130 L3/E∞ knife 125 — Loader account-17 owner limbs 0/1 after skip chain

## 目标

Knife 124 lands account-17 budget. Emit then loads account-17 owner limbs 0/1.

## 交付

1. `account17OwnerInputMem` / `walkAccount17OwnerAfterSkipChain?` /
   `evalWalkAccount17OwnerAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS owner-lo constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 125 section
- Spec guards for account-17 owner lo vs abs loads after septendecuple skip

## 仍未覆盖

account-17 owner hi/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
