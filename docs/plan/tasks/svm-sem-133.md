---
id: svm-sem-133
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-132]
---

# svm-sem-133 L3/E∞ knife 128 — Loader account-17 → account-18 skip chain

## 目标

Knife 127 completes account-17 fields after the skip chain. Emit chains the octodecuple skip geometry to reach the account-18 dup marker.

## 交付

1. `account18SkipNextInputMem / walkAccount18SkipNextAfterSkipChain?` / matching `evalAbsAccount18…?` helpers
2. Theorems：walk verified、POS constants、walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 128 section
- Spec guards for account-18 after octodecuple skip

## 仍未覆盖

account-18 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
