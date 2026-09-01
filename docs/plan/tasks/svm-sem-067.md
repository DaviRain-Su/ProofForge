---
id: svm-sem-067
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-066]
---

# svm-sem-067 L3/E∞ knife 62 — Loader account-8 owner limbs 0/1 after skip chain

## 目标

在 account-8 lamports/data_len 齐备之后，覆盖 Emit 对 account-8 owner limbs 0/1：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 octuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account8OwnerInputMem` / `walkAccount8OwnerAfterSkipChain?` /
   `evalWalkAccount8OwnerAfterSkipChainToStack?` / `evalAbsAccount8Owner?`
2. Theorems：`walkAccount8OwnerAfterSkipChain_verified`、
   `evalWalkAccount8_after_skip_owner0_0xEB_owner1_0xFC`、
   `walkAccount8OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 62 section
- Spec guards for owner0=0xEB / owner1=0xFC vs abs loads

## 仍未覆盖

account-8 owner limbs 2/3 or exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
