---
id: svm-sem-040
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-039]
---

# svm-sem-040 L3/E∞ knife 35 — Loader account-4 owner limbs 2/3 after skip chain

## 目标

在 account-4 owner 低 limbs 齐备之后，覆盖 Emit 对 account-4 的 owner 高 limbs：
`ldxdw` header+0x38 与 header+0x40。同一 quadruple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account4OwnerHiInputMem` / `walkAccount4OwnerHiAfterSkipChain?` /
   `evalWalkAccount4OwnerHiAfterSkipChainToStack?` / `evalAbsAccount4OwnerHi?`
2. Theorems：`walkAccount4OwnerHiAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_owner2_0x19_owner3_0x2A`、
   `walkAccount4OwnerHiAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 35 section
- Spec guards for owner2=0x19 / owner3=0x2A vs abs loads

## 仍未覆盖

account-4 executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
