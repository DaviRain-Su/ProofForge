---
id: svm-sem-128
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-127]
---

# svm-sem-128 L3/E∞ knife 123 — Loader account-17 signer/writable after skip chain

## 目标

Knife 122 lands account-17 meta. Emit then loads account-17 signer/writable flags.

## 交付

1. `account17FlagsInputMem` / `walkAccount17FlagsAfterSkipChain?` /
   `evalWalkAccount17FlagsAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS flag constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 123 section
- Spec guards for account-17 signer/writable vs abs loads after septendecuple skip

## 仍未覆盖

account-17 budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
