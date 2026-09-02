---
id: svm-sem-103
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-102]
---

# svm-sem-103 L3/E∞ knife 98 — Loader account-13 owner limbs 2/3 after skip chain

## 目标

Knife 97 completes account-13 owner limbs 0/1 after the skip chain. Emit then reads limbs 2/3。

## 交付

1. `account13OwnerHiInputMem` / `walkAccount13OwnerHiAfterSkipChain?` /
   `evalWalkAccount13OwnerHiAfterSkipChainToStack?` / `evalAbsAccount13OwnerHi?`
2. Theorems：`walkAccount13OwnerHiAfterSkipChain_verified`、`evalWalkAccount13_after_skip_owner2_0x22_owner3_0x33`、`walkAccount13OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 98 section
- Spec guards for owner2=0x22/owner3=0x33 vs abs loads

## 仍未覆盖

account-13 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
