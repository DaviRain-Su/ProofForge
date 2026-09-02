---
id: svm-sem-138
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-137]
---

# svm-sem-138 L3/E∞ knife 133 — Loader account-18 owner limbs 2/3 after skip chain

## 目标

Knife 132 lands account-18 owner lo. Emit then loads account-18 owner limbs 2/3.

## 交付

1. `account18OwnerHiInputMem / walkAccount18OwnerHiAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 133 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
