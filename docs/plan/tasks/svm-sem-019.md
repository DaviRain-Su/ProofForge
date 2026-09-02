---
id: svm-sem-019
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-018]
---

# svm-sem-019 L3/E∞ knife 14 — Loader account-1 owner limbs 2/3 after skip

## 目标

在 account-1 owner limbs 0/1（header-relative `+0x28` / `+0x30`）齐备之后，覆盖 Emit 对
account-1 的 owner 高字：header-relative `+0x38` / `+0x40`。同一 skip 推进的 `r2`
游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1OwnerHiInputMem` / `walkAccount1OwnerHiAfterSkip?` /
   `evalWalkAccount1OwnerHiAfterSkipToStack?` / `evalAbsAccount1OwnerHi?`
2. Theorems：`walkAccount1OwnerHiAfterSkip_verified`、
   `evalWalkAccount1_after_skip_owner2_0xC3_owner3_0xD4`、
   `walkAccount1OwnerHiAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 14 section
- Spec guards for owner2=`0xC3` / owner3=`0xD4` vs abs loads

## 仍未覆盖

account-1 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
