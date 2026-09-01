---
id: svm-sem-074
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-073]
---

# svm-sem-074 L3/E∞ knife 69 — Loader account-9 owner limbs 0/1 after skip chain

## 目标

在 account-9 lamports/data_len 齐备之后，覆盖 Emit 对 account-9 owner limbs 0/1：
`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9OwnerInputMem` / `walkAccount9OwnerAfterSkipChain?` /
   `evalWalkAccount9OwnerAfterSkipChainToStack?` / `evalAbsAccount9Owner?`
2. Theorems：`walkAccount9OwnerAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_owner0_0xEC_owner1_0xFD`、
   `walkAccount9OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 69 section
- Spec guards for owner0=0xEC / owner1=0xFD vs abs loads

## 仍未覆盖

account-9 owner hi/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
