---
id: svm-sem-123
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-122]
---

# svm-sem-123 L3/E∞ knife 118 — Loader account-16 owner limbs 0/1 after skip chain

## 目标

Knife 117 lands account-16 budget. Emit then loads account-16 owner limbs 0/1.

## 交付

1. `account16OwnerInputMem` / `walkAccount16OwnerAfterSkipChain?` /
   `evalWalkAccount16OwnerAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `owner lo` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 118 section
- Spec guards for account-16 owner lo vs abs loads after sedecuple skip

## 仍未覆盖

account-16 owner hi/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
