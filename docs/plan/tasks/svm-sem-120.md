---
id: svm-sem-120
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-119]
---

# svm-sem-120 L3/E∞ knife 115 — Loader account-16 header/key after skip chain

## 目标

Knife 114 proves the sedecuple skip lands on the account-16 dup marker. Emit then loads account-16 header/key.

## 交付

1. `account16MetaInputMem` / `walkAccount16MetaAfterSkipChain?` /
   `evalWalkAccount16MetaAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `header/key` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 115 section
- Spec guards for account-16 header/key vs abs loads after sedecuple skip

## 仍未覆盖

account-16 flags/budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
