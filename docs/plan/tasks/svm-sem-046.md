---
id: svm-sem-046
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-045]
---

# svm-sem-046 L3/E∞ knife 41 — Loader account-5 owner limbs 0/1 after skip chain

## 目标

在 account-5 lamports/data_len 齐备之后，覆盖 Emit 对 account-5 owner limbs 0/1：
`ldxdw` header+0x28 与 header+0x30。同一 quintuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account5OwnerInputMem` / `walkAccount5OwnerAfterSkipChain?` /
   `evalWalkAccount5OwnerAfterSkipChainToStack?` / `evalAbsAccount5Owner?`
2. Theorems：`walkAccount5OwnerAfterSkipChain_verified`、
   `evalWalkAccount5_after_skip_owner0_0xE8_owner1_0xF9`、
   `walkAccount5OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 41 section
- Spec guards for owner0=0xE8 / owner1=0xF9 vs abs loads

## 仍未覆盖

account-5 owner limbs 2/3/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
