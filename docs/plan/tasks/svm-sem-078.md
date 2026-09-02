---
id: svm-sem-078
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-077]
---

# svm-sem-078 L3/E∞ knife 73 — Loader account-10 header/key after skip chain

## 目标

Knife 72 proves the decuple skip lands on account-10 dup marker. Emit then treats that address as the account-10 header cursor (marker byte, key at `+8`).

## 交付

1. `account10MetaInputMem` / `walkAccount10MetaAfterSkipChain?` /
   `evalWalkAccount10MetaAfterSkipChainToStack?` / `evalAbsAccount10Meta?`
2. Theorems：`walkAccount10MetaAfterSkipChain_verified`、
   `evalWalkAccount10_after_skip_key_0x7A`、
   `walkAccount10MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 73 section
- Spec guards for key=0x7A / marker=0xB8 vs abs loads

## 仍未覆盖

account-10 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
