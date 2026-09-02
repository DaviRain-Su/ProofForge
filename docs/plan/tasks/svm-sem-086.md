---
id: svm-sem-086
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-085]
---

# svm-sem-086 L3/E∞ knife 81 — Loader account-11 signer/writable after skip chain

## 目标

Knife 80 lands the cursor on account-11 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable)。

## 交付

1. `account11FlagsInputMem` / `walkAccount11FlagsAfterSkipChain?` /
   `evalWalkAccount11FlagsAfterSkipChainToStack?` / `evalAbsAccount11Flags?`
2. Theorems：`walkAccount11FlagsAfterSkipChain_verified`、`evalWalkAccount11_after_skip_signer_writable_1`、`walkAccount11FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 81 section
- Spec guards for signer=1/writable=1 vs abs loads

## 仍未覆盖

account-11 budget/owner/exec-rent。
