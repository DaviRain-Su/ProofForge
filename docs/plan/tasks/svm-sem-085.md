---
id: svm-sem-085
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-084]
---

# svm-sem-085 L3/E∞ knife 80 — Loader account-11 header/key after skip chain

## 目标

Knife 79 proves the undecuple skip lands on account-11 dup marker. Emit then treats that
address as the account-11 header cursor (marker byte, key at `+8`)。

## 交付

1. `account11MetaInputMem` / `walkAccount11MetaAfterSkipChain?` /
   `evalWalkAccount11MetaAfterSkipChainToStack?` / `evalAbsAccount11Meta?`
2. Theorems：`walkAccount11MetaAfterSkipChain_verified`、`evalWalkAccount11_after_skip_key_0x7B`、`walkAccount11MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 80 section
- Spec guards for key=0x7B / marker=0xB9 vs abs loads

## 仍未覆盖

account-11 flags/budget/owner/exec-rent。
