---
id: svm-sem-081
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-080]
---

# svm-sem-081 L3/E∞ knife 76 — Loader account-10 owner limbs 0/1 after skip chain

## 目标

Knife 75 completes account-10 lamports/data_len. Emit then reads owner pubkey limbs 0 and 1.

## 交付

1. `account10OwnerInputMem` / `walkAccount10OwnerAfterSkipChain?` /
   `evalWalkAccount10OwnerAfterSkipChainToStack?` / `evalAbsAccount10Owner?`
2. Theorems：`walkAccount10OwnerAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_owner0_0xED_owner1_0xFE`、
   `walkAccount10OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 76 section
- Spec guards for owner0=0xED/owner1=0xFE vs abs loads

## 仍未覆盖

account-10 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
