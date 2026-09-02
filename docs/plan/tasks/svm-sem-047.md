---
id: svm-sem-047
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-046]
---

# svm-sem-047 L3/E∞ knife 42 — Loader account-5 owner limbs 2/3 after skip chain

## 目标

在 account-5 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-5 owner limbs 2/3：
`ldxdw` header+0x38 与 header+0x40。同一 quintuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account5OwnerHiInputMem` / `walkAccount5OwnerHiAfterSkipChain?` /
   `evalWalkAccount5OwnerHiAfterSkipChainToStack?` / `evalAbsAccount5OwnerHi?`
2. Theorems：`walkAccount5OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount5_after_skip_owner2_0x1A_owner3_0x2B`、
   `walkAccount5OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 42 section
- Spec guards for owner2=0x1A / owner3=0x2B vs abs loads

## 仍未覆盖

account-5 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
