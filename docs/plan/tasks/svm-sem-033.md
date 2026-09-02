---
id: svm-sem-033
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-032]
---

# svm-sem-033 L3/E∞ knife 28 — Loader account-3 owner limbs 2/3 after skip chain

## 目标

在 account-3 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-3 的 owner limbs 2/3：
`ldxdw` header+0x38 与 header+0x40。同一 triple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account3OwnerHiInputMem` / `walkAccount3OwnerHiAfterSkipChain?` /
   `evalWalkAccount3OwnerHiAfterSkipChainToStack?` / `evalAbsAccount3OwnerHi?`
2. Theorems：`walkAccount3OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount3_after_skip_owner2_0x18_owner3_0x29`、
   `walkAccount3OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 28 section
- Spec guards for owner2=`0x18`/owner3=`0x29` vs abs loads

## 仍未覆盖

account-3 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
