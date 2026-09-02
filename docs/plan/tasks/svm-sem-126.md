---
id: svm-sem-126
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-125]
---

# svm-sem-126 L3/E∞ knife 121 — Loader account-16 → account-17 skip chain

## 目标

Knife 120 completes account-16 fields after the skip chain. Emit chains the septendecuple skip geometry to reach the account-17 dup marker.

## 交付

1. `account16SkipNextInputMem` / `walkAccount16SkipNextAfterSkipChain?` /
   `evalWalkAccount16SkipNextAfterSkipChainToStack?` / matching `evalAbsAccount17…?` helpers
2. Theorems：walk verified、POS `marker` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 121 section
- Spec guards for account-17 marker vs abs loads after septendecuple skip

## 仍未覆盖

account-17 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
