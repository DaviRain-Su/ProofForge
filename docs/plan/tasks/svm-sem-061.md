---
id: svm-sem-061
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-060]
---

# svm-sem-061 L3/E∞ knife 56 — Loader account-7 owner limbs 2/3 after skip chain

## 目标

在 account-7 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-7 owner limbs 2/3：
`ldxdw` header+0x38 与 header+0x40。同一 septuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account7OwnerHiInputMem` / `walkAccount7OwnerHiAfterSkipChain?` /
   `evalWalkAccount7OwnerHiAfterSkipChainToStack?` / `evalAbsAccount7OwnerHi?`
2. Theorems：`walkAccount7OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_owner2_0x1C_owner3_0x2D`、
   `walkAccount7OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 56 section
- Spec guards for owner2=0x1C / owner3=0x2D vs abs loads

## 仍未覆盖

account-7 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
