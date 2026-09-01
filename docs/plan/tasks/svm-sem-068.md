---
id: svm-sem-068
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-067]
---

# svm-sem-068 L3/E∞ knife 63 — Loader account-8 owner limbs 2/3 after skip chain

## 目标

在 account-8 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-8 owner limbs 2/3：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 octuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account8OwnerHiInputMem` / `walkAccount8OwnerHiAfterSkipChain?` /
   `evalWalkAccount8OwnerHiAfterSkipChainToStack?` / `evalAbsAccount8OwnerHi?`
2. Theorems：`walkAccount8OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount8_after_skip_owner2_0x1D_owner3_0x2E`、
   `walkAccount8OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 63 section
- Spec guards for owner2=0x1D / owner3=0x2E vs abs loads

## 仍未覆盖

account-8 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
