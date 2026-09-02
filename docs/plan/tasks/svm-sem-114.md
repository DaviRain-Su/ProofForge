---
id: svm-sem-114
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-113]
---

# svm-sem-114 L3/E∞ knife 109 — Loader account-15 signer/writable after skip chain

## 目标

Knife 108 lands the cursor on account-15 meta. Emit then gates with `ldxb` of header+1 (signer) and +2 (writable).

## 交付

1. `account15FlagsInputMem` / `walkAccount15FlagsAfterSkipChain?` /
   `evalWalkAccount15FlagsAfterSkipChainToStack?` / `evalAbsAccount15Flags?`
2. Theorems + Spec `#guard`s

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 109 section

## 仍未覆盖

account-15 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
