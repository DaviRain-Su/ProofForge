---
id: svm-sem-082
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-081]
---

# svm-sem-082 L3/E∞ knife 77 — Loader account-10 owner limbs 2/3 after skip chain

## 目标

Knife 76 completes account-10 owner limbs 0/1. Emit then reads owner pubkey limbs 2 and 3.

## 交付

1. `account10OwnerHiInputMem` / `walkAccount10OwnerHiAfterSkipChain?` /
   `evalWalkAccount10OwnerHiAfterSkipChainToStack?` / `evalAbsAccount10OwnerHi?`
2. Theorems：`walkAccount10OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_owner2_0x1F_owner3_0x30`、
   `walkAccount10OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 77 section
- Spec guards for owner2=0x1F/owner3=0x30 vs abs loads

## 仍未覆盖

account-10 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
