---
id: svm-sem-134
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-133]
---

# svm-sem-134 L3/E∞ knife 129 — Loader account-18 header/key after skip chain

## 目标

Knife 128 proves the octodecuple skip lands on the account-18 dup marker. Emit then loads account-18 header/key.

## 交付

1. `account18MetaInputMem / walkAccount18MetaAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 129 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 flags/budget/owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
