---
id: svm-sem-117
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-116]
---

# svm-sem-117 L3/E∞ knife 112 — Loader account-15 owner limbs 2/3 after skip chain

## 目标

Knife 111 completes account-15 owner lo after the skip chain. Emit then reads owner pubkey limbs 2/3.

## 交付

1. `account15OwnerHiInputMem` / `walkAccount15OwnerHiAfterSkipChain?` /
   `evalWalkAccount15OwnerHiAfterSkipChainToStack?` / `evalAbsAccount15OwnerHi?`
2. Theorems + Spec `#guard`s

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 112 section

## 仍未覆盖

account-15 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
