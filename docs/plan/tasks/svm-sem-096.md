---
id: svm-sem-096
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-095]
---

# svm-sem-096 L3/E∞ knife 91 — Loader account-12 owner limbs 2/3 after skip chain

## 目标

Knife 90 completes account-12 owner lo after the skip chain. Emit then reads owner pubkey limbs 2/3。

## 交付

1. `account12OwnerHiInputMem` / `walkAccount12OwnerHiAfterSkipChain?` /
   `evalWalkAccount12OwnerHiAfterSkipChainToStack?` / `evalAbsAccount12OwnerHi?`
2. Theorems：`walkAccount12OwnerHiAfterSkipChain_verified`、`evalWalkAccount12_after_skip_owner2_0x21_owner3_0x32`、`walkAccount12OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 91 section
- Spec guards for owner2=0x21/owner3=0x32 vs abs loads

## 仍未覆盖

account-12 exec/rent。
