---
id: svm-sem-060
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-059]
---

# svm-sem-060 L3/E∞ knife 55 — Loader account-7 owner limbs 0/1 after skip chain

## 目标

在 account-7 lamports/data_len 齐备之后，覆盖 Emit 对 account-7 owner limbs 0/1：
`ldxdw` header+0x28 与 header+0x30。同一 septuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account7OwnerInputMem` / `walkAccount7OwnerAfterSkipChain?` /
   `evalWalkAccount7OwnerAfterSkipChainToStack?` / `evalAbsAccount7Owner?`
2. Theorems：`walkAccount7OwnerAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_owner0_0xEA_owner1_0xFB`、
   `walkAccount7OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 55 section
- Spec guards for owner0=0xEA / owner1=0xFB vs abs loads

## 仍未覆盖

account-7 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
