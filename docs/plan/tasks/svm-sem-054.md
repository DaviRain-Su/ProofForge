---
id: svm-sem-054
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-053]
---

# svm-sem-054 L3/E∞ knife 49 — Loader account-6 owner limbs 2/3 after skip chain

## 目标

在 account-6 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-6 owner limbs 2/3：
`ldxdw` header+0x38 与 header+0x40。同一 sextuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account6OwnerHiInputMem` / `walkAccount6OwnerHiAfterSkipChain?` /
   `evalWalkAccount6OwnerHiAfterSkipChainToStack?` / `evalAbsAccount6OwnerHi?`
2. Theorems：`walkAccount6OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_owner2_0x1B_owner3_0x2C`、
   `walkAccount6OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 49 section
- Spec guards for owner2=0x1B / owner3=0x2C vs abs loads

## 仍未覆盖

account-6 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
