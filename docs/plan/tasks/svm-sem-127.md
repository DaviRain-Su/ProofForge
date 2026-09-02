---
id: svm-sem-127
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-126]
---

# svm-sem-127 L3/E∞ knife 122 — Loader account-17 header/key after skip chain

## 目标

Knife 121 proves the septendecuple skip lands on the account-17 dup marker. Emit then loads account-17 header/key.

## 交付

1. `account17MetaInputMem` / `walkAccount17MetaAfterSkipChain?` /
   `evalWalkAccount17MetaAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS header/key constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 122 section
- Spec guards for account-17 header/key vs abs loads after septendecuple skip

## 仍未覆盖

account-17 flags/budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
