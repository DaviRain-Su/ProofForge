---
id: svm-sem-113
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-112]
---

# svm-sem-113 L3/E∞ knife 108 — Loader account-15 header/key after skip chain

## 目标

Knife 107 proves the quindecuple skip lands on the account-15 dup marker. Emit then treats that address as the account-15 header cursor (marker byte, key at `+8`).

## 交付

1. `account15MetaInputMem` / `walkAccount15MetaAfterSkipChain?` /
   `evalWalkAccount15MetaAfterSkipChainToStack?` / `evalAbsAccount15Meta?`
2. Theorems：`walkAccount15MetaAfterSkipChain_verified`、`evalWalkAccount15_after_skip_key_0x7F`、`walkAccount15MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 108 section
- Spec guards for key=0x7F / marker=0xBD vs abs loads

## 仍未覆盖

account-15 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
