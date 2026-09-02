---
id: svm-sem-109
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-108]
---

# svm-sem-109 L3/E∞ knife 104 — Loader account-14 owner limbs 0/1 after skip chain

## 目标

Knife 103 completes account-14 budget after the skip chain. Emit then reads owner pubkey limbs 0/1。

## 交付

1. `account14OwnerInputMem` / `walkAccount14OwnerAfterSkipChain?` /
   `evalWalkAccount14OwnerAfterSkipChainToStack?` / `evalAbsAccount14Owner?`
2. Theorems：`walkAccount14OwnerAfterSkipChain_verified`、`evalWalkAccount14_after_skip_owner0_0xF1_owner1_0x02`、`walkAccount14OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 104 section
- Spec guards for owner0=0xF1/owner1=0x02 vs abs loads

## 仍未覆盖

account-14 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
