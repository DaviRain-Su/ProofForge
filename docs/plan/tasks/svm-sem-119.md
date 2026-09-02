---
id: svm-sem-119
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-118]
---

# svm-sem-119 L3/E∞ knife 114 — Loader account-15 → account-16 skip chain

## 目标

Knife 113 completes account-15 fields after the skip chain. Emit chains the sedecuple skip geometry to reach the account-16 dup marker.

## 交付

1. `account15SkipNextInputMem` / `walkAccount15SkipNextAfterSkipChain?` /
   `evalWalkAccount15SkipNextAfterSkipChainToStack?` / matching `evalAbsAccount16…?` helpers
2. Theorems：walk verified、POS `marker` constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 114 section
- Spec guards for account-16 marker vs abs loads after sedecuple skip

## 仍未覆盖

account-16 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
