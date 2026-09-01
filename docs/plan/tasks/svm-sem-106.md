---
id: svm-sem-106
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-105]
---

# svm-sem-106 L3/E∞ knife 101 — Loader account-14 header/key after skip chain

## 目标

Knife 100 proves the quattuordecuple skip lands on the account-14 dup marker. Emit then treats that
address as the account-14 header cursor (marker byte, key at `+8`)。

## 交付

1. `account14MetaInputMem` / `walkAccount14MetaAfterSkipChain?` /
   `evalWalkAccount14MetaAfterSkipChainToStack?` / `evalAbsAccount14Meta?`
2. Theorems：`walkAccount14MetaAfterSkipChain_verified`、`evalWalkAccount14_after_skip_key_0x7E`、`walkAccount14MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 101 section
- Spec guards for key=0x7E / marker=0xBC vs abs loads

## 仍未覆盖

account-14 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
