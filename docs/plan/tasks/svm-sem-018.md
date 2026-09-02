---
id: svm-sem-018
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-017]
---

# svm-sem-018 L3/E∞ knife 13 — Loader account-1 owner limbs 0/1 after skip

## 目标

在 account-1 lamports/data_len（header-relative `+0x48` / `+0x50`）齐备之后，覆盖 Emit 对
account-1 的 owner 预算字：header-relative `+0x28` / `+0x30`。同一 skip 推进的 `r2`
游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1OwnerInputMem` / `walkAccount1OwnerAfterSkip?` /
   `evalWalkAccount1OwnerAfterSkipToStack?` / `evalAbsAccount1Owner?`
2. Theorems：`walkAccount1OwnerAfterSkip_verified`、
   `evalWalkAccount1_after_skip_owner0_0xA1_owner1_0xB2`、
   `walkAccount1OwnerAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 13 section
- Spec guards for owner0=`0xA1` / owner1=`0xB2` vs abs loads

## 仍未覆盖

account-1 owner limbs 2/3、executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
