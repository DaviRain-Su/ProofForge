---
id: svm-sem-137
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-136]
---

# svm-sem-137 L3/E∞ knife 132 — Loader account-18 owner limbs 0/1 after skip chain

## 目标

Knife 131 lands account-18 budget. Emit then loads account-18 owner limbs 0/1.

## 交付

1. `account18OwnerInputMem / walkAccount18OwnerAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 132 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 owner hi/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
