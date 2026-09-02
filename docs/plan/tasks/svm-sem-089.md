---
id: svm-sem-089
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-088]
---

# svm-sem-089 L3/E∞ knife 84 — Loader account-11 owner limbs 2/3 after skip chain

## 目标

Knife 83 completes account-11 owner limbs 0/1 after the skip chain. Emit then reads account-11
owner pubkey limbs 2 and 3（`+0x38` / `+0x40`）。

## 交付

1. `account11OwnerHiInputMem` / `walkAccount11OwnerHiAfterSkipChain?` /
   `evalWalkAccount11OwnerHiAfterSkipChainToStack?` / `evalAbsAccount11OwnerHi?`
2. Theorems：`walkAccount11OwnerHiAfterSkipChain_verified`、`evalWalkAccount11_after_skip_owner2_0x20_owner3_0x31`、`walkAccount11OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 84 section
- Spec guards for owner2=0x20/owner3=0x31 vs abs loads

## 仍未覆盖

account-11 exec/rent。
