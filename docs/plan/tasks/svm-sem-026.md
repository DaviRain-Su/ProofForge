---
id: svm-sem-026
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-025]
---

# svm-sem-026 L3/E∞ knife 21 — Loader account-2 owner limbs 2/3 after skip chain

## 目标

在 account-2 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-2 的 owner 高字：
header-relative `+0x38` / `+0x40`。同一 skip chain 推进的 `r2` 游标加载，并与绝对
`r6`-相对加载一致。

## 交付

1. `account2OwnerHiInputMem` / `walkAccount2OwnerHiAfterSkipChain?` /
   `evalWalkAccount2OwnerHiAfterSkipChainToStack?` / `evalAbsAccount2OwnerHi?`
2. Theorems：`walkAccount2OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_owner2_0x17_owner3_0x28`、
   `walkAccount2OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 21 section
- Spec guards for owner2=`0x17` / owner3=`0x28` vs abs loads

## 仍未覆盖

account-2 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
