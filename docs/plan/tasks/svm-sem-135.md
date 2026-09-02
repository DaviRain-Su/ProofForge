---
id: svm-sem-135
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-134]
---

# svm-sem-135 L3/E∞ knife 130 — Loader account-18 signer/writable after skip chain

## 目标

Knife 129 lands account-18 meta. Emit then loads account-18 signer/writable flags.

## 交付

1. `account18FlagsInputMem / walkAccount18FlagsAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 130 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
