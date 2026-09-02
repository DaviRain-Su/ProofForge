---
id: svm-sem-107
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-106]
---

# svm-sem-107 L3/E∞ knife 102 — Loader account-14 signer/writable after skip chain

## 目标

Knife 101 lands the cursor on account-14 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable)。

## 交付

1. `account14FlagsInputMem` / `walkAccount14FlagsAfterSkipChain?` /
   `evalWalkAccount14FlagsAfterSkipChainToStack?` / `evalAbsAccount14Flags?`
2. Theorems：`walkAccount14FlagsAfterSkipChain_verified`、`evalWalkAccount14_after_skip_signer_writable_1`、`walkAccount14FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 102 section
- Spec guards for signer/writable vs abs loads

## 仍未覆盖

account-14 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
