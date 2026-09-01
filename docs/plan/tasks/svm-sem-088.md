---
id: svm-sem-088
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-087]
---

# svm-sem-088 L3/E∞ knife 83 — Loader account-11 owner limbs 0/1 after skip chain

## 目标

Knife 82 completes account-11 lamports/data_len after the skip chain. Emit then reads account-11
owner pubkey limbs 0 and 1（`+0x28` / `+0x30`）。

## 交付

1. `account11OwnerInputMem` / `walkAccount11OwnerAfterSkipChain?` /
   `evalWalkAccount11OwnerAfterSkipChainToStack?` / `evalAbsAccount11Owner?`
2. Theorems：`walkAccount11OwnerAfterSkipChain_verified`、`evalWalkAccount11_after_skip_owner0_0xEE_owner1_0xFF`、`walkAccount11OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 83 section
- Spec guards for owner0=0xEE/owner1=0xFF vs abs loads

## 仍未覆盖

account-11 owner hi/exec-rent。
