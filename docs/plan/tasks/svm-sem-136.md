---
id: svm-sem-136
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-135]
---

# svm-sem-136 L3/E∞ knife 131 — Loader account-18 lamports/data_len after skip chain

## 目标

Knife 130 lands account-18 flags. Emit then loads account-18 lamports/data_len.

## 交付

1. `account18BudgetInputMem / walkAccount18BudgetAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 131 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 owner/exec；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
