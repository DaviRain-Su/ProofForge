---
id: svm-sem-102
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-101]
---

# svm-sem-102 L3/E∞ knife 97 — Loader account-13 owner limbs 0/1 after skip chain

## 目标

Knife 96 completes account-13 budget after the skip chain. Emit then reads owner pubkey limbs 0/1。

## 交付

1. `account13OwnerInputMem` / `walkAccount13OwnerAfterSkipChain?` /
   `evalWalkAccount13OwnerAfterSkipChainToStack?` / `evalAbsAccount13Owner?`
2. Theorems：`walkAccount13OwnerAfterSkipChain_verified`、`evalWalkAccount13_after_skip_owner0_0xF0_owner1_0x01`、`walkAccount13OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 97 section
- Spec guards for owner0=0xF0/owner1=0x01 vs abs loads

## 仍未覆盖

account-13 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
