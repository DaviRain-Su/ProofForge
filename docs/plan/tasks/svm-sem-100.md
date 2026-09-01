---
id: svm-sem-100
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-099]
---

# svm-sem-100 L3/E∞ knife 95 — Loader account-13 signer/writable after skip chain

## 目标

Knife 94 lands the cursor on account-13 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable)。

## 交付

1. `account13FlagsInputMem` / `walkAccount13FlagsAfterSkipChain?` /
   `evalWalkAccount13FlagsAfterSkipChainToStack?` / `evalAbsAccount13Flags?`
2. Theorems：`walkAccount13FlagsAfterSkipChain_verified`、`evalWalkAccount13_after_skip_signer_writable_1`、`walkAccount13FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 95 section
- Spec guards for signer=1/writable=1 (POS) vs signer=1/writable=0 (EQ)

## 仍未覆盖

account-13 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
