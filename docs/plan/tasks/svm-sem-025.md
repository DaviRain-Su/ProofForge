---
id: svm-sem-025
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-024]
---

# svm-sem-025 L3/E∞ knife 20 — Loader account-2 owner limbs 0/1 after skip chain

## 目标

在 account-2 lamports/data_len 齐备之后，覆盖 Emit 对 account-2 的 owner 预算字：
header-relative `+0x28` / `+0x30`。同一 skip chain 推进的 `r2` 游标加载，并与绝对
`r6`-相对加载一致。

## 交付

1. `account2OwnerInputMem` / `walkAccount2OwnerAfterSkipChain?` /
   `evalWalkAccount2OwnerAfterSkipChainToStack?` / `evalAbsAccount2Owner?`
2. Theorems：`walkAccount2OwnerAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_owner0_0xE5_owner1_0xF6`、
   `walkAccount2OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 20 section
- Spec guards for owner0=`0xE5` / owner1=`0xF6` vs abs loads

## 仍未覆盖

account-2 owner limbs 2/3、executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
