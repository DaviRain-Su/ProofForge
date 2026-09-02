---
id: svm-sem-121
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-120]
---

# svm-sem-121 L3/E∞ knife 116 — Loader account-16 signer/writable after skip chain

## 目标

Knife 115 lands account-16 meta. Emit then loads account-16 signer/writable flags.

## 交付

1. `account16FlagsInputMem` / `walkAccount16FlagsAfterSkipChain?` /
   `evalWalkAccount16FlagsAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `signer/writable` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 116 section
- Spec guards for account-16 signer/writable vs abs loads after sedecuple skip

## 仍未覆盖

account-16 budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
