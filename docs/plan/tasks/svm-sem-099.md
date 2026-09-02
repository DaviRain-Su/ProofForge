---
id: svm-sem-099
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-098]
---

# svm-sem-099 L3/E∞ knife 94 — Loader account-13 header/key after skip chain

## 目标

Knife 93 proves the tredecuple skip lands on the account-13 dup marker. Emit then treats that
address as the account-13 header cursor (marker byte, key at `+8`)。

## 交付

1. `account13MetaInputMem` / `walkAccount13MetaAfterSkipChain?` /
   `evalWalkAccount13MetaAfterSkipChainToStack?` / `evalAbsAccount13Meta?`
2. Theorems：`walkAccount13MetaAfterSkipChain_verified`、`evalWalkAccount13_after_skip_key_0x7D`、`walkAccount13MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 94 section
- Spec guards for key=0x7D / marker=0xBB vs abs loads

## 仍未覆盖

account-13 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
