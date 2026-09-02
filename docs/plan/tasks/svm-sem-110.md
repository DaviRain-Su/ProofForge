---
id: svm-sem-110
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-109]
---

# svm-sem-110 L3/E∞ knife 105 — Loader account-14 owner limbs 2/3 after skip chain

## 目标

Knife 104 completes account-14 owner lo after the skip chain. Emit then reads owner pubkey limbs 2/3。

## 交付

1. `account14OwnerHiInputMem` / `walkAccount14OwnerHiAfterSkipChain?` /
   `evalWalkAccount14OwnerHiAfterSkipChainToStack?` / `evalAbsAccount14OwnerHi?`
2. Theorems：`walkAccount14OwnerHiAfterSkipChain_verified`、`evalWalkAccount14_after_skip_owner2_0x23_owner3_0x34`、`walkAccount14OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 105 section
- Spec guards for owner2=0x23/owner3=0x34 vs abs loads

## 仍未覆盖

account-14 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
