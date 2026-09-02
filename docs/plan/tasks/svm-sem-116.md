---
id: svm-sem-116
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-115]
---

# svm-sem-116 L3/E∞ knife 111 — Loader account-15 owner limbs 0/1 after skip chain

## 目标

Knife 110 completes account-15 budget after the skip chain. Emit then reads owner pubkey limbs 0/1.

## 交付

1. `account15OwnerInputMem` / `walkAccount15OwnerAfterSkipChain?` /
   `evalWalkAccount15OwnerAfterSkipChainToStack?` / `evalAbsAccount15Owner?`
2. Theorems + Spec `#guard`s

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 111 section

## 仍未覆盖

account-15 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
