---
id: svm-sem-095
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-094]
---

# svm-sem-095 L3/E∞ knife 90 — Loader account-12 owner limbs 0/1 after skip chain

## 目标

Knife 89 completes account-12 budget after the skip chain. Emit then reads owner pubkey limbs 0/1。

## 交付

1. `account12OwnerInputMem` / `walkAccount12OwnerAfterSkipChain?` /
   `evalWalkAccount12OwnerAfterSkipChainToStack?` / `evalAbsAccount12Owner?`
2. Theorems：`walkAccount12OwnerAfterSkipChain_verified`、`evalWalkAccount12_after_skip_owner0_0xEF_owner1_0x00`、`walkAccount12OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 90 section
- Spec guards for owner0=0xEF/owner1=0x00 vs abs loads

## 仍未覆盖

account-12 owner hi/exec-rent。
