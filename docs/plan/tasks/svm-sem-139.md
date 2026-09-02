---
id: svm-sem-139
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-138]
---

# svm-sem-139 L3/E∞ knife 134 — Loader account-18 executable/rent after skip chain

## 目标

Knife 133 lands account-18 owner hi. Emit then loads account-18 executable/rent_epoch.

## 交付

1. `account18ExecRentInputMem / walkAccount18ExecRentAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 134 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18→account-19 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
