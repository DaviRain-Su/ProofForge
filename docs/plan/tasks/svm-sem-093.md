---
id: svm-sem-093
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-092]
---

# svm-sem-093 L3/E∞ knife 88 — Loader account-12 signer/writable after skip chain

## 目标

Knife 87 lands the cursor on account-12 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable)。

## 交付

1. `account12FlagsInputMem` / `walkAccount12FlagsAfterSkipChain?` /
   `evalWalkAccount12FlagsAfterSkipChainToStack?` / `evalAbsAccount12Flags?`
2. Theorems：`walkAccount12FlagsAfterSkipChain_verified`、`evalWalkAccount12_after_skip_signer_writable_1`、`walkAccount12FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 88 section
- Spec guards for signer=1/writable=1 vs abs loads (EQ writable=0)

## 仍未覆盖

account-12 budget/owner/exec-rent。
