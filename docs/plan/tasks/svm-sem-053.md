---
id: svm-sem-053
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-052]
---

# svm-sem-053 L3/E∞ knife 48 — Loader account-6 owner limbs 0/1 after skip chain

## 目标

在 account-6 lamports/data_len 齐备之后，覆盖 Emit 对 account-6 owner limbs 0/1：
`ldxdw` header+0x28 与 header+0x30。同一 sextuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account6OwnerInputMem` / `walkAccount6OwnerAfterSkipChain?` /
   `evalWalkAccount6OwnerAfterSkipChainToStack?` / `evalAbsAccount6Owner?`
2. Theorems：`walkAccount6OwnerAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_owner0_0xE9_owner1_0xFA`、
   `walkAccount6OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 48 section
- Spec guards for owner0=0xE9 / owner1=0xFA vs abs loads

## 仍未覆盖

account-6 owner limbs 2/3/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
