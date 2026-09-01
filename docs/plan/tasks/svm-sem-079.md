---
id: svm-sem-079
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-078]
---

# svm-sem-079 L3/E∞ knife 74 — Loader account-10 signer/writable after skip chain

## 目标

Knife 73 lands the cursor on account-10 meta. Emit then gates with `ldxb` of header+1 (signer) and +2 (writable).

## 交付

1. `account10FlagsInputMem` / `walkAccount10FlagsAfterSkipChain?` /
   `evalWalkAccount10FlagsAfterSkipChainToStack?` / `evalAbsAccount10Flags?`
2. Theorems：`walkAccount10FlagsAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_signer_writable_1`、
   `walkAccount10FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 74 section
- Spec guards for signer/writable vs abs loads

## 仍未覆盖

account-10 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
