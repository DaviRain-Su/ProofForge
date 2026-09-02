---
id: svm-sem-075
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-074]
---

# svm-sem-075 L3/E∞ knife 70 — Loader account-9 owner limbs 2/3 after skip chain

## 目标

在 account-9 owner limbs 0/1 齐备之后，覆盖 Emit 对 account-9 owner limbs 2/3：
`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9OwnerHiInputMem` / `walkAccount9OwnerHiAfterSkipChain?` /
   `evalWalkAccount9OwnerHiAfterSkipChainToStack?` / `evalAbsAccount9OwnerHi?`
2. Theorems：`walkAccount9OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_owner2_0x1E_owner3_0x2F`、
   `walkAccount9OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 70 section
- Spec guards for owner2=0x1E / owner3=0x2F vs abs loads

## 仍未覆盖

account-9 exec/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
