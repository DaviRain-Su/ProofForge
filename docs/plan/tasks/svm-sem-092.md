---
id: svm-sem-092
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-091]
---

# svm-sem-092 L3/E∞ knife 87 — Loader account-12 header/key after skip chain

## 目标

Knife 86 proves the duodecuple skip lands on the account-12 dup marker. Emit then treats that
address as the account-12 header cursor (marker byte, key at `+8`)。

## 交付

1. `account12MetaInputMem` / `walkAccount12MetaAfterSkipChain?` /
   `evalWalkAccount12MetaAfterSkipChainToStack?` / `evalAbsAccount12Meta?`
2. Theorems：`walkAccount12MetaAfterSkipChain_verified`、`evalWalkAccount12_after_skip_key_0x7C`、`walkAccount12MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 87 section
- Spec guards for key=0x7C / marker=0xBA vs abs loads

## 仍未覆盖

account-12 flags/budget/owner/exec-rent。
